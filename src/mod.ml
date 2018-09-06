open Utils
open SmartPrint

module Value = struct
  type 'a t =
    | Variable of 'a
    | Function of 'a * Effect.PureType.t
    | Type of 'a
    | Descriptor
    | Constructor
    | Field

  let map (f : 'a -> 'b) (v : 'a t) : 'b t =
    match v with
    | Variable a -> Variable (f a)
    | Function (a, typ) -> Function (f a, typ)
    | Type a -> Type (f a)
    | Descriptor -> Descriptor
    | Constructor -> Constructor
    | Field -> Field

  let to_string (v : 'a t) : string =
    match v with
    | Variable _ -> "variable"
    | Function _ -> "function"
    | Type _ -> "type"
    | Descriptor -> "descriptor"
    | Constructor -> "constructor"
    | Field -> "field"
end
open Value

module Locator = struct
  type t = {
    vars : PathName.t PathName.Map.t;
    typs : PathName.t PathName.Map.t;
    descriptors : PathName.t PathName.Map.t;
    constructors : PathName.t PathName.Map.t;
    fields : PathName.t PathName.Map.t;
    modules : PathName.t PathName.Map.t }

  let empty = {
    vars = PathName.Map.empty;
    typs = PathName.Map.empty;
    descriptors = PathName.Map.empty;
    constructors = PathName.Map.empty;
    fields = PathName.Map.empty;
    modules = PathName.Map.empty }

  let join
    (f : PathName.t PathName.Map.t -> PathName.t PathName.Map.t ->
      PathName.t PathName.Map.t)
    (l1 : t) (l2 : t) : t = {
    vars = f l1.vars l2.vars;
    typs = f l1.typs l2.typs;
    descriptors = f l1.descriptors l2.descriptors;
    constructors = f l1.constructors l2.constructors;
    fields = f l1.fields l2.fields;
    modules = f l1.modules l2.modules }

  let pp (l : t) : SmartPrint.t =
    let pp_map map = PathName.Map.bindings map |> OCaml.list (fun (x, y) ->
      nest (PathName.pp x ^^ !^ "=" ^^ PathName.pp y)) in
    OCaml.list (fun x -> x) [
      !^ "vars:" ^^ pp_map l.vars;
      !^ "typs:" ^^ pp_map l.typs;
      !^ "descriptors:" ^^ pp_map l.descriptors;
      !^ "constructors:" ^^ pp_map l.constructors;
      !^ "fields:" ^^ pp_map l.fields;
      !^ "modules" ^^ pp_map l.modules ]
end

type 'a t = {
  name : CoqName.t option;
  coq_path : Name.t list;
  locator : Locator.t;
  values : 'a Value.t PathName.Map.t;
  modules : 'a t PathName.Map.t }

let empty (module_name : CoqName.t option) (coq_path : Name.t list)
  : 'a t =
  let coq_path = match module_name with
    | Some module_name ->
      let (ocaml_name, coq_name) = CoqName.assoc_names module_name in
      coq_path @ [coq_name]
    | None -> coq_path in
  {
    name = module_name;
    coq_path = coq_path;
    locator = Locator.empty;
    values = PathName.Map.empty;
    modules = PathName.Map.empty
  }

let pp (m : 'a t) : SmartPrint.t =
  OCaml.list (fun x -> x) [
    group (!^ "module:" ^^ separate (!^ ".") (List.map Name.pp m.coq_path));
    group @@ !^ "modules:" ^^ nest (OCaml.list (fun (x, _) -> PathName.pp x) @@
      PathName.Map.bindings m.modules);
    group @@ !^ "values:" ^^ group (OCaml.list (fun (x, _) -> PathName.pp x) @@
      PathName.Map.bindings m.values);
    Locator.pp m.locator ]

let name (m : 'a t) : CoqName.t =
  match m.name with
  | Some name -> name
  | None -> failwith "No name associated with this module."

let rec map (f : 'a -> 'b) (m : 'a t) : 'b t =
  { m with
    values = m.values |> PathName.Map.map (Value.map f);
    modules = PathName.Map.map (map f) m.modules }

module type Carrier = sig
  val resolve_opt : PathName.t -> 'a t -> PathName.t option
  val mem : PathName.t -> 'a t -> bool
end

module type ValueCarrier = sig
  include Carrier
  val value : 'a -> 'a Value.t
  val assoc : PathName.t -> PathName.t -> 'a -> 'a t -> 'a t
  val find : PathName.t -> 'a t -> 'a
end

module type EmptyCarrier = sig
  include Carrier
  val value : 'a Value.t
  val assoc : PathName.t -> PathName.t -> 'a t -> 'a t
end

module Vars = struct
  let resolve_opt (x : PathName.t) (m : 'a t) : PathName.t option =
    PathName.Map.find_opt x m.locator.vars

  let value (v : 'a) : 'a Value.t = Variable v

  let assoc (x : PathName.t) (y : PathName.t) (v : 'a) (m : 'a t) : 'a t =
    { m with
      values = PathName.Map.add y (Variable v) m.values;
      locator = { m.locator with
        vars = PathName.Map.add x y m.locator.vars } }

  let mem (x : PathName.t) (m : 'a t) : bool =
    match PathName.Map.find_opt x m.values with
    | Some (Variable _ | Function _) -> true
    | _ -> false

  let find (x : PathName.t) (m : 'a t) : 'a =
    match PathName.Map.find x m.values with
    | Variable a -> a
    | Function (a, _) -> a
    | _ -> failwith @@
      String.concat "." x.PathName.path ^ "." ^ x.PathName.base ^ " is not a Variable"
end
module Function = struct
  let value (v : 'a) (typ : Effect.PureType.t) : 'a Value.t = Function (v, typ)

  let assoc (x : PathName.t) (y : PathName.t) (v : 'a)
    (typ : Effect.PureType.t) (m : 'a t) : 'a t =
    { m with
      values = PathName.Map.add y (Function (v, typ)) m.values;
      locator = { m.locator with
        vars = PathName.Map.add x y m.locator.vars } }

  let find (x : PathName.t) (m : 'a t) : Effect.PureType.t option =
    match PathName.Map.find x m.values with
    | Variable _ -> None
    | Function (_, typ) -> Some typ
    | _ -> failwith @@
      String.concat "." x.PathName.path ^ "." ^ x.PathName.base ^ " is not a Variable"
end
module Typs = struct
  let resolve_opt (x : PathName.t) (m : 'a t) : PathName.t option =
    PathName.Map.find_opt x m.locator.typs

  let value (v : 'a) : 'a Value.t = Type v

  let assoc (x : PathName.t) (y : PathName.t) (v : 'a) (m : 'a t) : 'a t =
    { m with
      values = PathName.Map.add y (Type v) m.values;
      locator = { m.locator with
        typs = PathName.Map.add x y m.locator.typs } }

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
    PathName.Map.find_opt x m.locator.descriptors

  let value : 'a Value.t = Descriptor

  let assoc (x : PathName.t) (y : PathName.t) (m : 'a t) : 'a t =
    { m with
      values = PathName.Map.add y Descriptor m.values;
      locator = { m.locator with
        descriptors = PathName.Map.add x y m.locator.descriptors } }

  let mem (x : PathName.t) (m : 'a t) : bool =
    match PathName.Map.find_opt x m.values with
    | Some Descriptor -> true
    | _ -> false
end
module Constructors = struct
  let resolve_opt (x : PathName.t) (m : 'a t) : PathName.t option =
    PathName.Map.find_opt x m.locator.constructors

  let value : 'a Value.t = Constructor

  let assoc (x : PathName.t) (y : PathName.t) (m : 'a t) : 'a t =
    { m with
      values = PathName.Map.add y Constructor m.values;
      locator = { m.locator with
        constructors = PathName.Map.add x y m.locator.constructors } }

  let mem (x : PathName.t) (m : 'a t) : bool =
    match PathName.Map.find_opt x m.values with
    | Some Constructor -> true
    | _ -> false
end
module Fields = struct
  let resolve_opt (x : PathName.t) (m : 'a t) : PathName.t option =
    PathName.Map.find_opt x m.locator.fields

  let value : 'a Value.t = Field

  let assoc (x : PathName.t) (y : PathName.t) (m : 'a t) : 'a t =
    { m with
      values = PathName.Map.add y Field m.values;
      locator = { m.locator with
        fields = PathName.Map.add x y m.locator.fields } }

  let mem (x : PathName.t) (m : 'a t) : bool =
    match PathName.Map.find_opt x m.values with
    | Some Field -> true
    | _ -> false
end
module Modules = struct
  let resolve_opt (x : PathName.t) (m : 'a t) : PathName.t option =
    PathName.Map.find_opt x m.locator.modules

  let assoc (x : PathName.t) (y : PathName.t) (v : 'a t) (m : 'a t) : 'a t =
    { m with
      modules = PathName.Map.add y v m.modules;
      locator = { m.locator with
        modules = PathName.Map.add x y m.locator.modules } }

  let mem (x : PathName.t) (m : 'a t) : bool = PathName.Map.mem x m.modules

  let find_opt (x : PathName.t) (m : 'a t) : 'a t option =
    PathName.Map.find_opt x m.modules

  let find (x : PathName.t) (m : 'a t) : 'a t =
    PathName.Map.find x m.modules
end

let finish_module (prefix : 'a -> 'a) (m1 : 'a t) (m2 : 'a t)
  : 'a t =
  match option_map CoqName.ocaml_name m1.name with
  | Some module_name ->
    let add_to_path x =
      { x with PathName.path = module_name :: x.PathName.path } in
    let m =
    { name = m2.name;
      coq_path = m2.coq_path;
      locator = Locator.join
        (PathName.Map.map_union add_to_path (fun _ v -> v))
        m1.locator m2.locator;
      values = PathName.Map.union (fun _ v _ -> Some (Value.map prefix v))
        m1.values m2.values;
      modules = PathName.Map.union (fun _ v _ -> Some v) m1.modules m2.modules
    } in
    Modules.assoc (PathName.of_name [] module_name)
      (PathName.of_name_list m1.coq_path) m1 m
  | None -> (* This is a partial module, do not add name information. *)
    { name = m2.name;
      coq_path = m2.coq_path;
      locator = Locator.join (PathName.Map.union (fun _ v _ -> Some v))
        m1.locator m2.locator;
      values = PathName.Map.map_union (fun x -> x)
        (fun _ v -> Value.map prefix v)
        m1.values m2.values;
      modules = PathName.Map.union (fun _ v _ -> Some v)
        m1.modules m2.modules }

let map_values (f : 'a -> 'a) (m : 'a t) : 'a t =
  { m with values = m.values |> PathName.Map.map (Value.map f) }
