open SmartPrint
open Utils

type 'a t = {
  values : 'a Mod.Value.t PathName.Map.t;
  modules : Mod.t PathName.Map.t;
  active_module : FullMod.t;
  bound_external :
    Name.Set.t ref -> (PathName.t -> Mod.t -> PathName.t option) ->
    (PathName.t -> Mod.t -> bool) -> PathName.t -> BoundName.t option;
  find_external : Loc.t -> BoundName.t -> 'a Mod.Value.t;
  find_external_module : Loc.t -> BoundName.t -> Mod.t;
  (* TODO: Move away from using a reference here by updating and passing env
     explicitly, possibly as a monad. *)
  required_modules : Name.Set.t ref
}

let pp (env : 'a t) : SmartPrint.t = FullMod.pp env.active_module

let empty (module_name : CoqName.t option)
  (get_module : Name.t -> Mod.t option) : 'a t = {
  values = PathName.Map.empty;
  modules = PathName.Map.empty;
  active_module = FullMod.empty module_name [];
  bound_external = (fun _ _ _ _ -> None);
  find_external = (fun loc x ->
    let message = BoundName.pp x ^^ !^ "not found." in
    Error.raise loc (SmartPrint.to_string 80 2 message));
  find_external_module = (fun loc x ->
    let message = !^ "Module" ^^ BoundName.pp x ^^ !^ "not found." in
    Error.raise loc (SmartPrint.to_string 80 2 message));
  required_modules = ref Name.Set.empty
}

let module_required (module_name : Name.t) (env : 'a t) : unit =
  env.required_modules := Name.Set.add module_name !(env.required_modules)

let requires (env : 'a t) : Name.t list =
  Name.Set.elements !(env.required_modules)

let coq_path (env : 'a t) : Name.t list = FullMod.coq_path env.active_module

let update_active (f : Mod.t -> Mod.t) (env : 'a t) : 'a t =
  { env with active_module = FullMod.hd_mod_map f env.active_module }

let enter_module (module_name : CoqName.t) (env : 'a t) : 'a t =
  {env with active_module = FullMod.enter_module module_name env.active_module}

let enter_section (env : 'a t) : 'a t =
  {env with active_module = FullMod.enter_section env.active_module}

let localize (has_name : PathName.t -> Mod.t -> bool) (x : BoundName.t)
  (env : 'a t) : BoundName.t =
  FullMod.localize has_name env.active_module x

let bound_name_opt (find : PathName.t -> Mod.t -> PathName.t option)
  (has_name : PathName.t -> Mod.t -> bool) (x : PathName.t) (env : 'a t)
  : BoundName.t option =
  match FullMod.bound_name_opt find x env.active_module with
  | Some name -> Some (localize has_name name env)
  | None -> env.bound_external env.required_modules find has_name x

let bound_name (find : PathName.t -> Mod.t -> PathName.t option)
  (has_name : PathName.t -> Mod.t -> bool) (loc : Loc.t) (x : PathName.t)
  (env : 'a t) : BoundName.t =
  match bound_name_opt find has_name x env with
  | Some name -> name
  | None ->
    let message = PathName.pp x ^^ !^ "not found." in
    Error.raise loc (SmartPrint.to_string 80 2 message)

let map (f : 'a -> 'b) (env : 'a t) : 'b t =
  { env with
    values = PathName.Map.map (Mod.Value.map f) env.values;
    find_external = (fun loc x -> Mod.Value.map f @@ env.find_external loc x)
    }

let combine (env1 : 'a t) (env2 : 'a t) : 'a t =
  env1.required_modules := Name.Set.union !(env1.required_modules)
    !(env2.required_modules);
  { env1 with
    values = PathName.Map.union (fun _ _ x -> Some x) env1.values env2.values;
    modules = PathName.Map.union (fun _ _ x -> Some x) env1.modules
      env2.modules;
    active_module = FullMod.combine env1.active_module env2.active_module;
  }

let include_module (x : Mod.t) (env : 'a t) : 'a t =
  { env with active_module = FullMod.include_module x env.active_module }

let find_free_name (path : Name.t list) (base_name : string) (env : 'a t)
  : Name.t =
  let path = coq_path env @ path in
  let prefix_n s n =
    if n = 0 then
      Name.of_string s
    else
      Name.of_string @@ Printf.sprintf "%s_%d" s n in
  let rec first_n (n : int) : Name.t =
    let name = prefix_n base_name n in
    if PathName.Map.mem (PathName.of_name path name) env.values then
      first_n (n + 1)
    else name in
  first_n 0

let find_free_path (x : PathName.t) (env : 'a t) : PathName.t =
  {
    PathName.path = coq_path env @ x.PathName.path;
    base = find_free_name x.PathName.path x.PathName.base env
  }

let find (loc : Loc.t) (x : BoundName.t) (env : 'a t) : 'a Mod.Value.t =
  match PathName.Map.find_opt x.full_path env.values with
  | Some v -> v
  | None -> env.find_external loc x

module Carrier (M : Mod.Carrier) = struct
  let resolve (path : Name.t list) (base : Name.t) (env : 'a t) : PathName.t =
    let x = PathName.of_name path base in
    match FullMod.hd_map (M.resolve_opt x) env.active_module with
    | Some path -> path
    | None -> find_free_path x env

  let has_name (env : 'a t) (x : PathName.t) (m : Mod.t) =
    let x = { x with PathName.path = m.Mod.coq_path @ x.PathName.path } in
    PathName.Map.mem x env.values

  let bound_opt (x : PathName.t) (env : 'a t) : BoundName.t option =
    bound_name_opt M.resolve_opt (has_name env) x env

  let bound (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
    bound_name M.resolve_opt (has_name env) loc x env
end

module ValueCarrier (M : Mod.ValueCarrier) = struct
  include Carrier(M)
  let raw_add (x : PathName.t) (y : PathName.t) (v : 'a) (env : 'a t) : 'a t =
    { env with
      values = PathName.Map.add y (M.value v) env.values;
      active_module = FullMod.hd_mod_map (M.assoc x y) env.active_module }

  let add (path : Name.t list) (base : Name.t) (v : 'a) (env : 'a t) : 'a t =
    raw_add (PathName.of_name path base) (resolve path base env) v env

  let assoc (path : Name.t list) (base : Name.t) (assoc_base : Name.t) (v : 'a)
    (env : 'a t) : 'a t =
    raw_add (PathName.of_name path base)
      (PathName.of_name (coq_path env @ path) assoc_base) v env

  let find (loc : Loc.t) (x : BoundName.t) (env : 'a t) : 'a =
    M.unpack @@ find loc x env

  (** Add a fresh local name beginning with [prefix] in [env]. *)
  let fresh (prefix : string) (v : 'a) (env : 'a t) : Name.t * 'a t =
    let name = find_free_name [] prefix env in
    (name, add [] name v env)
end

module Var = ValueCarrier(Mod.Vars)
module Typ = ValueCarrier(Mod.Typs)

module Function = struct
  include Carrier(Mod.Vars)

  let raw_add (x : PathName.t) (y : PathName.t) (v : 'a)
    (typ : Effect.PureType.t) (env : 'a t) : 'a t =
    { env with
      values = PathName.Map.add y (Mod.Function.value v typ) env.values;
      active_module = FullMod.hd_mod_map (Mod.Function.assoc x y)
        env.active_module }

  let add (path : Name.t list) (base : Name.t) (v : 'a)
    (typ : Effect.PureType.t) (env : 'a t) : 'a t =
    raw_add (PathName.of_name path base) (resolve path base env) v typ env

  let assoc (path : Name.t list) (base : Name.t) (assoc_base : Name.t) (v : 'a)
    (typ : Effect.PureType.t) (env : 'a t) : 'a t =
    raw_add (PathName.of_name path base)
      (PathName.of_name (coq_path env @ path) assoc_base) v typ env

  let find (loc : Loc.t) (x : BoundName.t) (env : 'a t)
    : Effect.PureType.t option =
    Mod.Function.unpack @@ find loc x env

  (** Add a fresh local name beginning with [prefix] in [env]. *)
  let fresh (prefix : string) (v : 'a) (typ : Effect.PureType.t) (env : 'a t)
    : Name.t * 'a t =
    let name = find_free_name [] prefix env in
    (name, add [] name v typ env)
end

module EmptyCarrier (M : Mod.EmptyCarrier) = struct
  include Carrier(M)
  let raw_add (x : PathName.t) (y : PathName.t) (env : 'a t) : 'a t =
    { env with
      values = PathName.Map.add y M.value env.values;
      active_module = FullMod.hd_mod_map (M.assoc x y) env.active_module }

  let add (path : Name.t list) (base : Name.t) (env : 'a t) : 'a t =
    raw_add (PathName.of_name path base) (resolve path base env) env

  let assoc (path : Name.t list) (base : Name.t) (assoc_base : Name.t)
    (env : 'a t) : 'a t =
    raw_add (PathName.of_name path base)
      (PathName.of_name (coq_path env @ path) assoc_base) env

  (** Add a fresh local name beginning with [prefix] in [env]. *)
  let fresh (prefix : string) (env : 'a t) : Name.t * 'a t =
    let name = find_free_name [] prefix env in
    (name, add [] name env)
end

module Descriptor = EmptyCarrier(Mod.Descriptors)
module Constructor = EmptyCarrier(Mod.Constructors)
module Field = EmptyCarrier(Mod.Fields)

module Module = struct
  let resolve (path : Name.t list) (base : Name.t) (env : 'a t) : PathName.t =
    let x = PathName.of_name path base in
    match FullMod.hd_map (Mod.Modules.resolve_opt x) env.active_module with
    | Some path -> path
    | None -> { path = coq_path env @ x.path; base = x.base }

  let has_name (env : 'a t) (x : PathName.t) (m : Mod.t) =
    let x = { x with PathName.path = m.Mod.coq_path @ x.PathName.path } in
    PathName.Map.mem x env.modules

  let bound_opt (x : PathName.t) (env : 'a t) : BoundName.t option =
    bound_name_opt Mod.Modules.resolve_opt (has_name env) x env

  let bound (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
    bound_name Mod.Modules.resolve_opt (has_name env) loc x env

  let raw_add (x : PathName.t) (y : PathName.t) (v : Mod.t) (env : 'a t)
    : 'a t =
    { env with
      modules = PathName.Map.add y v env.modules;
      active_module =
        FullMod.hd_mod_map (Mod.Modules.assoc x y) env.active_module }

  let add (path : Name.t list) (base : Name.t) (v : Mod.t) (env : 'a t)
    : 'a t =
    raw_add (PathName.of_name path base) (resolve path base env) v env

  let assoc (path : Name.t list) (base : Name.t) (assoc_base : Name.t)
    (v : Mod.t) (env : 'a t) : 'a t =
    raw_add (PathName.of_name path base)
      (PathName.of_name (coq_path env @ path) assoc_base) v env

  let find (loc : Loc.t) (x : BoundName.t) (env : 'a t) : Mod.t =
    match PathName.Map.find_opt x.full_path env.modules with
    | Some v -> v
    | None -> env.find_external_module loc x

  (** Add a fresh local name beginning with [prefix] in [env]. *)
  let fresh (prefix : string) (v : Mod.t) (env : 'a t) : Name.t * 'a t =
    let path = coq_path env in
    let rec first_n (n : int) : Name.t =
      let name = if n = 0 then
          Name.of_string prefix
        else
          Name.of_string @@ Printf.sprintf "%s_%d" prefix n in
      if PathName.Map.mem (PathName.of_name path name) env.modules then
        first_n (n + 1)
      else name in
    let name = first_n 0 in
    (name, add [] name v env)
end

let open_module (loc : Loc.t) (module_name : BoundName.t) (env : 'a t) : 'a t =
  let m = Module.find loc module_name env in
  { env with active_module =
      FullMod.open_module m module_name.depth env.active_module }

let open_module' (loc : Loc.t) (module_name : Name.t list) (env : 'a t) : 'a t =
  let path = PathName.of_name_list module_name in
  open_module loc (Module.bound loc path env) env

let leave_module (localize : FullMod.t -> 'a -> 'a) (env : 'a t) : 'a t =
  let (m, active_module) = FullMod.leave_module env.active_module in
  let values = Mod.fold (fun _ x -> PathName.Map.update x
      (option_map (Mod.Value.map (localize active_module))))
    m env.values in
  let env = { env with active_module; values } in
  let module_name = match option_map CoqName.ocaml_name m.Mod.name with
    | Some module_name -> module_name
    | None -> failwith "Leaving a module with no name." in
  Module.raw_add (PathName.of_name [] module_name)
    (PathName.of_name_list m.coq_path) m env

let add_exception (path : Name.t list) (base : Name.t) (env : unit t) : unit t =
  env
  |> Descriptor.add path base
  |> Var.add path ("raise_" ^ base) ()

let add_exception_with_effects (path : Name.t list) (base : Name.t)
  (env : Effect.Type.t t) : Effect.Type.t t =
  let env = Descriptor.add path base env in
  let descriptor = PathName.of_name path base in
  let bound_descriptor = Descriptor.bound Loc.Unknown descriptor env in
  let effect_typ =
    Effect.Type.Arrow (
      Effect.Descriptor.singleton bound_descriptor [],
      Effect.Type.Pure) in
  Var.add path ("raise_" ^ base) effect_typ env
