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

type t = {
  name : CoqName.t option;
  coq_path : Name.t list;
  vars : PathName.t PathName.Map.t;
  typs : PathName.t PathName.Map.t;
  descriptors : PathName.t PathName.Map.t;
  constructors : PathName.t PathName.Map.t;
  fields : PathName.t PathName.Map.t;
  modules : PathName.t PathName.Map.t;
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
    vars = PathName.Map.empty;
    typs = PathName.Map.empty;
    descriptors = PathName.Map.empty;
    constructors = PathName.Map.empty;
    fields = PathName.Map.empty;
    modules = PathName.Map.empty;
  }

let join
  (f : PathName.t PathName.Map.t -> PathName.t PathName.Map.t ->
    PathName.t PathName.Map.t)
  (l1 : t) (l2 : t) : t = { l2 with
  vars = f l1.vars l2.vars;
  typs = f l1.typs l2.typs;
  descriptors = f l1.descriptors l2.descriptors;
  constructors = f l1.constructors l2.constructors;
  fields = f l1.fields l2.fields;
  modules = f l1.modules l2.modules }

let fold (f : PathName.t -> PathName.t -> 'a -> 'a) (m : t) (a : 'a) : 'a =
  let a = PathName.Map.fold f m.vars a in
  let a = PathName.Map.fold f m.typs a in
  let a = PathName.Map.fold f m.descriptors a in
  let a = PathName.Map.fold f m.constructors a in
  let a = PathName.Map.fold f m.fields a in
  let a = PathName.Map.fold f m.modules a in
  a

let pp (m : t) : SmartPrint.t =
  let pp_map map = PathName.Map.bindings map |> OCaml.list (fun (x, y) ->
    nest (PathName.pp x ^^ !^ "=" ^^ PathName.pp y)) in
  OCaml.list (fun x -> x) [
    group (!^ "module:" ^^ separate (!^ ".") (List.map Name.pp m.coq_path));
    !^ "vars:" ^^ pp_map m.vars;
    !^ "typs:" ^^ pp_map m.typs;
    !^ "descriptors:" ^^ pp_map m.descriptors;
    !^ "constructors:" ^^ pp_map m.constructors;
    !^ "fields:" ^^ pp_map m.fields;
    !^ "modules" ^^ pp_map m.modules ]

let name (m : t) : CoqName.t =
  match m.name with
  | Some name -> name
  | None -> failwith "No name associated with this module."

let combine (m1 : t) (m2 : t) : t =
  join (PathName.Map.union (fun _ name _ -> Some name)) m2 m1

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
    PathName.Map.find_opt x m.vars

  let value (v : 'a) : 'a Value.t = Variable v

  let assoc (x : PathName.t) (y : PathName.t) (m : t) : t =
    { m with vars = PathName.Map.add x y m.vars }

  let unpack (v : 'a Value.t) : 'a =
    match v with
    | Variable a -> a
    | Function (a, _) -> a
    | _ -> failwith @@ "Could not interpret " ^ Value.to_string v ^ " as a variable."
end
module Function = struct
  let value (v : 'a) (typ : Effect.PureType.t) : 'a Value.t = Function (v, typ)

  let assoc (x : PathName.t) (y : PathName.t) (m : t) : t =
    { m with vars = PathName.Map.add x y m.vars }

  let unpack (v : 'a Value.t) : Effect.PureType.t option =
    match v with
    | Variable _ -> None
    | Function (_, typ) -> Some typ
    | _ -> failwith @@ "Could not interpret " ^ Value.to_string v ^ " as a variable."
end
module Typs = struct
  let resolve_opt (x : PathName.t) (m : t) : PathName.t option =
    PathName.Map.find_opt x m.typs

  let value (v : 'a) : 'a Value.t = Type v

  let assoc (x : PathName.t) (y : PathName.t) (m : t) : t =
    { m with typs = PathName.Map.add x y m.typs }

  let unpack (v : 'a Value.t) : 'a =
    match v with
    | Type a -> a
    | _ -> failwith @@ "Could not interpret " ^ Value.to_string v ^ " as a type."
end
module Descriptors = struct
  let resolve_opt (x : PathName.t) (m : t) : PathName.t option =
    PathName.Map.find_opt x m.descriptors

  let value : 'a Value.t = Descriptor

  let assoc (x : PathName.t) (y : PathName.t) (m : t) : t =
    { m with descriptors = PathName.Map.add x y m.descriptors }
end
module Constructors = struct
  let resolve_opt (x : PathName.t) (m : t) : PathName.t option =
    PathName.Map.find_opt x m.constructors

  let value : 'a Value.t = Constructor

  let assoc (x : PathName.t) (y : PathName.t) (m : t) : t =
    { m with constructors = PathName.Map.add x y m.constructors }
end
module Fields = struct
  let resolve_opt (x : PathName.t) (m : t) : PathName.t option =
    PathName.Map.find_opt x m.fields

  let value : 'a Value.t = Field

  let assoc (x : PathName.t) (y : PathName.t) (m : t) : t =
    { m with fields = PathName.Map.add x y m.fields }
end
module Modules = struct
  let resolve_opt (x : PathName.t) (m : t) : PathName.t option =
    PathName.Map.find_opt x m.modules

  let assoc (x : PathName.t) (y : PathName.t) (m : t) : t =
    { m with modules = PathName.Map.add x y m.modules }
end

let finish_module (m1 : t) (m2 : t) : t =
  match option_map CoqName.ocaml_name m1.name with
  | Some module_name ->
    let add_to_path x =
      { x with PathName.path = module_name :: x.PathName.path } in
    join (PathName.Map.map_union add_to_path (fun _ v -> v)) m1 m2
  | None -> (* This is a partial module, do not add name information. *)
    join (PathName.Map.union (fun _ v _ -> Some v)) m1 m2
