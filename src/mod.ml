open Utils
open SmartPrint

module Value = struct
  type 'a t =
    | Variable of 'a
    | Type of 'a
    | Descriptor
    | Constructor
    | Field

  let map (f : 'a -> 'b) (v : 'a t) : 'b t =
    match v with
    | Variable a -> Variable (f a)
    | Type a -> Type (f a)
    | Descriptor -> Descriptor
    | Constructor -> Constructor
    | Field -> Field

  let to_string (v : 'a t) : string =
    match v with
    | Variable _ -> "variable"
    | Type _ -> "type"
    | Descriptor -> "descriptor"
    | Constructor -> "constructor"
    | Field -> "field"
end
open Value

module Locator = struct
  type t = {
    vars : Name.t PathName.Map.t;
    typs : Name.t PathName.Map.t;
    descriptors : Name.t PathName.Map.t;
    constructors : Name.t PathName.Map.t;
    fields : Name.t PathName.Map.t }

  let empty = {
    vars = PathName.Map.empty;
    typs = PathName.Map.empty;
    descriptors = PathName.Map.empty;
    constructors = PathName.Map.empty;
    fields = PathName.Map.empty }

  let join (f : Name.t PathName.Map.t -> Name.t PathName.Map.t -> Name.t PathName.Map.t)
    (l1 : t) (l2 : t) : t = {
    vars = f l1.vars l2.vars;
    typs = f l1.typs l2.typs;
    descriptors = f l1.descriptors l2.descriptors;
    constructors = f l1.constructors l2.constructors;
    fields = f l1.fields l2.fields }
end

type 'a t = {
  opens : Name.t list list;
  external_opens : Name.t list list;
  locator : Locator.t;
  values : 'a Value.t PathName.Map.t;
  modules : 'a t PathName.Map.t }

let empty : 'a t = {
  opens = [[]]; (** By default we open the empty path. *)
  external_opens = [[]];
  locator = Locator.empty;
  values = PathName.Map.empty;
  modules = PathName.Map.empty }

let pp (m : 'a t) : SmartPrint.t =
  let pp_map = OCaml.list PathName.pp in
  let vars = ref [] in
  let typs = ref [] in
  let descriptors = ref [] in
  let constructors = ref [] in
  let fields = ref [] in
  m.values |> PathName.Map.iter (fun x v ->
    match v with
    | Variable _ -> vars := x :: !vars
    | Type _ -> typs := x :: !typs
    | Descriptor -> descriptors := x :: !descriptors
    | Constructor -> constructors := x :: !constructors
    | Field -> fields := x :: !fields);
  group (
    nest (!^ "open" ^^ OCaml.list (fun path ->
      double_quotes (separate (!^ ".") (List.map Name.pp path)))
      m.opens) ^^ newline ^^
    nest (!^ "open (external)" ^^ OCaml.list (fun path ->
      double_quotes (separate (!^ ".") (List.map Name.pp path)))
      m.external_opens) ^^ newline ^^
    !^ "vars:" ^^ nest (pp_map !vars) ^^ newline ^^
    !^ "typs:" ^^ nest (pp_map !typs) ^^ newline ^^
    !^ "descriptors:" ^^ nest (pp_map !descriptors) ^^ newline ^^
    !^ "constructors:" ^^ nest (pp_map !constructors) ^^ newline ^^
    !^ "fields:" ^^ nest (pp_map !fields) ^^ newline ^^
    !^ "modules:" ^^ nest (OCaml.list (fun (x, _) -> PathName.pp x) @@
      PathName.Map.bindings m.modules))

let open_module (m : 'a t) (module_name : Name.t list) : 'a t =
  { m with opens = module_name :: m.opens }

let open_external_module (m : 'a t) (module_name : Name.t list) : 'a t =
  { m with external_opens = module_name :: m.external_opens }

let find_free_name (base_name : string) (env : 'a t) : Name.t =
  let prefix_n s n =
    if n = 0 then
      Name.of_string s
    else
      Name.of_string @@ Printf.sprintf "%s_%d" s n in
  let rec first_n (n : int) : int =
    if PathName.Map.mem (PathName.of_name [] @@ prefix_n base_name n) env.values then
      first_n (n + 1)
    else
      n in
  prefix_n base_name (first_n 0)

let find_free_path (x : PathName.t) (env : 'a t) : PathName.t =
  { x with base = find_free_name x.base env }

let rec map (f : 'a -> 'b) (m : 'a t) : 'b t =
  { m with
    values = m.values |> PathName.Map.map (Value.map f);
    modules = PathName.Map.map (map f) m.modules }

module Vars = struct
  let resolve_opt (x : PathName.t) (m : 'a t) : PathName.t option =
    option_map (fun name -> { x with base = name }) @@
      PathName.Map.find_opt x m.locator.vars

  let resolve (x : PathName.t) (m : 'a t) : PathName.t =
    match resolve_opt x m with
    | Some path -> path
    | None -> find_free_path x m

  let assoc (x : PathName.t) (y : PathName.t) (v : 'a) (m : 'a t) : 'a t =
    { m with
      values = PathName.Map.add y (Variable v) m.values;
      locator = { m.locator with
        vars = PathName.Map.add x y.base m.locator.vars } }

  let add (x : PathName.t) (v : 'a) (m : 'a t) : 'a t =
    let y = match resolve_opt x m with
      | Some path -> path
      | None -> find_free_path x m in
    assoc x y v m

  let mem (x : PathName.t) (m : 'a t) : bool =
    match PathName.Map.find_opt x m.values with
    | Some (Variable _) -> true
    | _ -> false

  let find (x : PathName.t) (m : 'a t) : 'a =
    match PathName.Map.find x m.values with
    | Variable a -> a
    | _ -> failwith @@
      String.concat "." x.PathName.path ^ "." ^ x.PathName.base ^ " is not a Variable"

  (** Add a fresh local name beginning with [prefix] in [env]. *)
  let fresh (prefix : string) (v : 'a) (env : 'a t) : Name.t * 'a t =
    let name = find_free_name prefix env in
    (name, add (PathName.of_name [] name) v env)
end
module Typs = struct
  let resolve_opt (x : PathName.t) (m : 'a t) : PathName.t option =
    option_map (fun name -> { x with base = name }) @@
      PathName.Map.find_opt x m.locator.typs

  let resolve (x : PathName.t) (m : 'a t) : PathName.t =
    match resolve_opt x m with
    | Some path -> path
    | None -> find_free_path x m

  let assoc (x : PathName.t) (y : PathName.t) (v : 'a) (m : 'a t) : 'a t =
    { m with
      values = PathName.Map.add y (Type v) m.values;
      locator = { m.locator with
        typs = PathName.Map.add x y.base m.locator.typs } }

  let add (x : PathName.t) (v : 'a) (m : 'a t) : 'a t =
    let y = match resolve_opt x m with
      | Some path -> path
      | None -> find_free_path x m in
    assoc x y v m

  let mem (x : PathName.t) (m : 'a t) : bool =
    match PathName.Map.find_opt x m.values with
    | Some (Type _) -> true
    | _ -> false

  let find (x : PathName.t) (m : 'a t) : 'a =
    match PathName.Map.find x m.values with
    | Type a -> a
    | _ -> failwith @@
      String.concat "." x.PathName.path ^ "." ^ x.PathName.base ^ " is not a Type"
end
module Descriptors = struct
  let resolve_opt (x : PathName.t) (m : 'a t) : PathName.t option =
    option_map (fun name -> { x with base = name }) @@
      PathName.Map.find_opt x m.locator.descriptors

  let add (x : PathName.t) (m : 'a t) : 'a t =
    let y = match resolve_opt x m with
      | Some path -> path
      | None -> find_free_path x m in
    { m with
      values = PathName.Map.add y Descriptor m.values;
      locator = { m.locator with
        descriptors = PathName.Map.add x y.base m.locator.descriptors } }

  let mem (x : PathName.t) (m : 'a t) : bool =
    match PathName.Map.find_opt x m.values with
    | Some Descriptor -> true
    | _ -> false
end
module Constructors = struct
  let resolve_opt (x : PathName.t) (m : 'a t) : PathName.t option =
    option_map (fun name -> { x with base = name }) @@
      PathName.Map.find_opt x m.locator.constructors

  let resolve (x : PathName.t) (m : 'a t) : PathName.t =
    match resolve_opt x m with
    | Some path -> path
    | None -> find_free_path x m

  let assoc (x : PathName.t) (y : PathName.t) (m : 'a t) : 'a t =
    { m with
      values = PathName.Map.add y Constructor m.values;
      locator = { m.locator with
        constructors = PathName.Map.add x y.base m.locator.constructors } }

  let add (x : PathName.t) (m : 'a t) : 'a t =
    let y = match resolve_opt x m with
      | Some path -> path
      | None -> find_free_path x m in
    assoc x y m

  let mem (x : PathName.t) (m : 'a t) : bool =
    match PathName.Map.find_opt x m.values with
    | Some Constructor -> true
    | _ -> false
end
module Fields = struct
  let resolve_opt (x : PathName.t) (m : 'a t) : PathName.t option =
    option_map (fun name -> { x with base = name }) @@
      PathName.Map.find_opt x m.locator.fields

  let resolve (x : PathName.t) (m : 'a t) : PathName.t =
    match resolve_opt x m with
    | Some path -> path
    | None -> find_free_path x m

  let assoc (x : PathName.t) (y : PathName.t) (m : 'a t) : 'a t =
    { m with
      values = PathName.Map.add y Field m.values;
      locator = { m.locator with
        fields = PathName.Map.add x y.base m.locator.fields } }

  let add (x : PathName.t) (m : 'a t) : 'a t =
    let y = match resolve_opt x m with
      | Some path -> path
      | None -> find_free_path x m in
    assoc x y m

  let mem (x : PathName.t) (m : 'a t) : bool =
    match PathName.Map.find_opt x m.values with
    | Some Field -> true
    | _ -> false
end
module Modules = struct
  let add (x : PathName.t) (v : 'a t) (m : 'a t) : 'a t =
    { m with modules = PathName.Map.add x v m.modules }

  let mem (x : PathName.t) (m : 'a t) : bool =
    PathName.Map.mem x m.modules

  let resolve_opt (x : PathName.t) (m : 'a t) : PathName.t option =
    if mem x m then Some x else None

  let find (x : PathName.t) (m : 'a t) : 'a t =
    PathName.Map.find x m.modules
end

let finish_module (module_name : Name.t) (prefix : Name.t -> 'a -> 'a)
  (m1 : 'a t) (m2 : 'a t) : 'a t =
  let add_to_path x =
    { x with PathName.path = module_name :: x.PathName.path } in
  let m =
  { opens = m2.opens;
    external_opens = m2.external_opens;
    locator = Locator.join
      (PathName.Map.map_union add_to_path (fun _ v -> v))
      m1.locator m2.locator;
    values = PathName.Map.map_union add_to_path
      (fun _ v -> Value.map (prefix module_name) v)
      m1.values m2.values;
    modules = PathName.Map.map_union add_to_path (fun _ v -> v)
      m1.modules m2.modules } in
  Modules.add (PathName.of_name [] module_name) m1 m

exception NameConflict of string * string * PathName.t

let include_module (m_incl : 'a t) (m : 'a t) : 'a t =
  { opens = m.opens;
    external_opens = m.external_opens;
    values = PathName.Map.union (fun key v1 v2 ->
      raise (NameConflict (Value.to_string v1, Value.to_string v2, key)))
     m_incl.values m.values;
    locator = Locator.join (fun v1 v2 -> v1 (* will fail in values *))
      m_incl.locator m.locator;
    modules = PathName.Map.union (fun key _ _ ->
        raise (NameConflict ("module", "module", key)))
      m_incl.modules m.modules }
