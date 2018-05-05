open SmartPrint

type 'a t = {
  opens : Name.t list list;
  vars : 'a PathName.Map.t;
  typs : unit PathName.Map.t;
  descriptors: unit PathName.Map.t;
  constructors : unit PathName.Map.t;
  fields : unit PathName.Map.t;
  modules : 'a t PathName.Map.t }

let empty : 'a t = {
  opens = [[]]; (** By default we open the empty path. *)
  vars = PathName.Map.empty;
  typs = PathName.Map.empty;
  descriptors = PathName.Map.empty;
  constructors = PathName.Map.empty;
  fields = PathName.Map.empty;
  modules = PathName.Map.empty }

let pp (m : 'a t) : SmartPrint.t =
  let pp_map map = OCaml.list (fun (x, _) -> PathName.pp x)
    (PathName.Map.bindings map) in
  group (
    nest (!^ "open" ^^ OCaml.list (fun path ->
      double_quotes (separate (!^ ".") (List.map Name.pp path)))
      m.opens) ^^ newline ^^
    !^ "vars:" ^^ nest (pp_map m.vars) ^^ newline ^^
    !^ "typs:" ^^ nest (pp_map m.typs) ^^ newline ^^
    !^ "descriptors:" ^^ nest (pp_map m.descriptors) ^^ newline ^^
    !^ "constructors:" ^^ nest (pp_map m.constructors) ^^ newline ^^
    !^ "fields:" ^^ nest (pp_map m.fields) ^^ newline ^^
    !^ "modules:" ^^ nest (pp_map m.modules))

let open_module (m : 'a t) (module_name : Name.t list) : 'a t =
  { m with opens = module_name :: m.opens }

let find_free_name (base_name : string) (env : 'a PathName.Map.t) : Name.t =
  let prefix_n s n =
    if n = 0 then
      Name.of_string s
    else
      Name.of_string @@ Printf.sprintf "%s_%d" s n in
  let rec first_n (n : int) : int =
    if PathName.Map.mem (PathName.of_name [] @@ prefix_n base_name n) env then
      first_n (n + 1)
    else
      n in
  prefix_n base_name (first_n 0)

let rec map (f : 'a -> 'b) (m : 'a t) : 'b t =
  { m with
    vars = PathName.Map.map f m.vars;
    modules = PathName.Map.map (map f) m.modules }

module Vars = struct
  let add (x : PathName.t) (v : 'a) (m : 'a t) : 'a t =
    { m with vars = PathName.Map.add x v m.vars }

  let mem (x : PathName.t) (m : 'a t) : bool =
    PathName.Map.mem x m.vars

  let find (x : PathName.t) (m : 'a t) : 'a =
    PathName.Map.find x m.vars

  (** Add a fresh local name beginning with [prefix] in [env]. *)
  let fresh (prefix : string) (v : 'a) (env : 'a t) : Name.t * 'a t =
    let name = find_free_name prefix env.vars in
    (name, add (PathName.of_name [] name) v env)
end
module Typs = struct
  let add (x : PathName.t) (m : 'a t) : 'a t =
    { m with typs = PathName.Map.add x () m.typs }

  let mem (x : PathName.t) (m : 'a t) : bool =
    PathName.Map.mem x m.typs
end
module Descriptors = struct
  let add (x : PathName.t) (m : 'a t) : 'a t =
    { m with descriptors = PathName.Map.add x () m.descriptors }

  let mem (x : PathName.t) (m : 'a t) : bool =
    PathName.Map.mem x m.descriptors
end
module Constructors = struct
  let add (x : PathName.t) (m : 'a t) : 'a t =
    { m with constructors = PathName.Map.add x () m.constructors }

  let mem (x : PathName.t) (m : 'a t) : bool =
    PathName.Map.mem x m.constructors
end
module Fields = struct
  let add (x : PathName.t) (m : 'a t) : 'a t =
    { m with fields = PathName.Map.add x () m.fields }

  let mem (x : PathName.t) (m : 'a t) : bool =
    PathName.Map.mem x m.fields
end
module Modules = struct
  let add (x : PathName.t) (v : 'a t) (m : 'a t) : 'a t =
    { m with modules = PathName.Map.add x v m.modules }

  let mem (x : PathName.t) (m : 'a t) : bool =
    PathName.Map.mem x m.modules

  let find (x : PathName.t) (m : 'a t) : 'a t =
    PathName.Map.find x m.modules
end

let finish_module (module_name : Name.t) (prefix : Name.t -> 'a -> 'a)
  (m1 : 'a t) (m2 : 'a t) : 'a t =
  let add_to_path x =
    { x with PathName.path = module_name :: x.PathName.path } in
  let unit_map_union = PathName.Map.map_union add_to_path (fun _ () -> ()) in
  let m =
  { opens = m2.opens;
    vars = PathName.Map.map_union add_to_path
      (fun _ v -> prefix module_name v) m1.vars m2.vars;
    typs = unit_map_union m1.typs m2.typs;
    descriptors = unit_map_union m1.descriptors m2.descriptors;
    constructors = unit_map_union m1.constructors m2.constructors;
    fields = unit_map_union m1.fields m2.fields;
    modules = PathName.Map.map_union add_to_path (fun _ v -> v)
      m1.modules m2.modules } in
  Modules.add (PathName.of_name [] module_name) m1 m

exception NameConflict of string * PathName.t

let include_module (m_incl : 'a t) (m : 'a t) : 'a t =
  let reject_dups typ key _ _ = raise (NameConflict (typ, key)) in
  { opens = m.opens;
    vars = PathName.Map.union (reject_dups "variable")
      m_incl.vars m.vars;
    typs = PathName.Map.union (reject_dups "type")
      m_incl.typs m.typs;
    descriptors = PathName.Map.union (reject_dups "descriptor")
      m_incl.descriptors m.descriptors;
    constructors = PathName.Map.union (reject_dups "constructor")
      m_incl.constructors m.constructors;
    fields = PathName.Map.union (reject_dups "field")
      m_incl.fields m.fields;
    modules = PathName.Map.union (reject_dups "module")
      m_incl.modules m.modules }
