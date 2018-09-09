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

  let fold (f : PathName.t -> PathName.t -> 'a -> 'a) (l : t) (a : 'a) : 'a =
    let a = PathName.Map.fold f l.vars a in
    let a = PathName.Map.fold f l.typs a in
    let a = PathName.Map.fold f l.descriptors a in
    let a = PathName.Map.fold f l.constructors a in
    let a = PathName.Map.fold f l.fields a in
    let a = PathName.Map.fold f l.modules a in
    a

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

type t = {
  name : CoqName.t option;
  coq_path : Name.t list;
  locator : Locator.t;
}

let empty (module_name : CoqName.t option) (coq_path : Name.t list) : t =
  let coq_path = match module_name with
    | Some module_name ->
      let (ocaml_name, coq_name) = CoqName.assoc_names module_name in
      coq_path @ [coq_name]
    | None -> coq_path in
  {
    name = module_name;
    coq_path = coq_path;
    locator = Locator.empty;
  }

let pp (m : t) : SmartPrint.t =
  OCaml.list (fun x -> x) [
    group (!^ "module:" ^^ separate (!^ ".") (List.map Name.pp m.coq_path));
    Locator.pp m.locator ]

let name (m : t) : CoqName.t =
  match m.name with
  | Some name -> name
  | None -> failwith "No name associated with this module."

let combine (m1 : t) (m2 : t) : t =
  { m1 with
    locator = Locator.join (PathName.Map.union (fun _ _ name -> Some name))
      m1.locator m2.locator
  }

module type Carrier = sig
  val resolve_opt : PathName.t -> t -> PathName.t option
  val assoc : PathName.t -> PathName.t -> t -> t
end

module type ValueCarrier = sig
  include Carrier
  val value : 'a -> 'a Value.t
  val unpack : 'a Value.t -> 'a
end

module type EmptyCarrier = sig
  include Carrier
  val value : 'a Value.t
end

module Vars = struct
  let resolve_opt (x : PathName.t) (m : t) : PathName.t option =
    PathName.Map.find_opt x m.locator.vars

  let value (v : 'a) : 'a Value.t = Variable v

  let assoc (x : PathName.t) (y : PathName.t) (m : t) : t =
    { m with
      locator = { m.locator with
        vars = PathName.Map.add x y m.locator.vars } }

  let unpack (v : 'a Value.t) : 'a =
    match v with
    | Variable a -> a
    | Function (a, _) -> a
    | _ -> failwith @@ "Could not interpret " ^ Value.to_string v ^ " as a variable."
end
module Function = struct
  let value (v : 'a) (typ : Effect.PureType.t) : 'a Value.t = Function (v, typ)

  let assoc (x : PathName.t) (y : PathName.t) (v : 'a)
    (typ : Effect.PureType.t) (m : t) : t =
    { m with
      locator = { m.locator with
        vars = PathName.Map.add x y m.locator.vars } }

  let unpack (v : 'a Value.t) : Effect.PureType.t option =
    match v with
    | Variable _ -> None
    | Function (_, typ) -> Some typ
    | _ -> failwith @@ "Could not interpret " ^ Value.to_string v ^ " as a variable."
end
module Typs = struct
  let resolve_opt (x : PathName.t) (m : t) : PathName.t option =
    PathName.Map.find_opt x m.locator.typs

  let value (v : 'a) : 'a Value.t = Type v

  let assoc (x : PathName.t) (y : PathName.t) (m : t) : t =
    { m with
      locator = { m.locator with
        typs = PathName.Map.add x y m.locator.typs } }

  let unpack (v : 'a Value.t) : 'a =
    match v with
    | Type a -> a
    | _ -> failwith @@ "Could not interpret " ^ Value.to_string v ^ " as a type."
end
module Descriptors = struct
  let resolve_opt (x : PathName.t) (m : t) : PathName.t option =
    PathName.Map.find_opt x m.locator.descriptors

  let value : 'a Value.t = Descriptor

  let assoc (x : PathName.t) (y : PathName.t) (m : t) : t =
    { m with
      locator = { m.locator with
        descriptors = PathName.Map.add x y m.locator.descriptors } }
end
module Constructors = struct
  let resolve_opt (x : PathName.t) (m : t) : PathName.t option =
    PathName.Map.find_opt x m.locator.constructors

  let value : 'a Value.t = Constructor

  let assoc (x : PathName.t) (y : PathName.t) (m : t) : t =
    { m with
      locator = { m.locator with
        constructors = PathName.Map.add x y m.locator.constructors } }
end
module Fields = struct
  let resolve_opt (x : PathName.t) (m : t) : PathName.t option =
    PathName.Map.find_opt x m.locator.fields

  let value : 'a Value.t = Field

  let assoc (x : PathName.t) (y : PathName.t) (m : t) : t =
    { m with
      locator = { m.locator with
        fields = PathName.Map.add x y m.locator.fields } }
end
module Modules = struct
  let resolve_opt (x : PathName.t) (m : t) : PathName.t option =
    PathName.Map.find_opt x m.locator.modules

  let assoc (x : PathName.t) (y : PathName.t) (v : t) (m : t) : t =
    { m with
      locator = { m.locator with
        modules = PathName.Map.add x y m.locator.modules } }
end

let finish_module (m1 : t) (m2 : t) : t =
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
    } in
    Modules.assoc (PathName.of_name [] module_name)
      (PathName.of_name_list m1.coq_path) m1 m
  | None -> (* This is a partial module, do not add name information. *)
    { name = m2.name;
      coq_path = m2.coq_path;
      locator = Locator.join (PathName.Map.union (fun _ v _ -> Some v))
        m1.locator m2.locator;
    }

let fold (f : PathName.t -> PathName.t -> 'b -> 'b) (m : t) (a : 'b) : 'b =
  Locator.fold f m.locator a
