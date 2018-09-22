open SmartPrint
open Utils

type 'a t = {
  values : 'a Mod.Value.t PathName.Map.t;
  modules : Mod.t PathName.Map.t;
  active_module : FullMod.t;
  load_module : Name.t -> Effect.t t -> Effect.t t;
  run_in_external :
    'b. (Effect.t t -> 'b * Effect.t t) -> 'a t -> 'b option;
  convert : Effect.t -> 'a;
  (* TODO: Move away from using a reference here by updating and passing env
     explicitly, possibly as a monad. *)
  required_modules : Name.Set.t ref;
  interfaces : (Name.t * string) list
}

let pp (env : 'a t) : SmartPrint.t = FullMod.pp env.active_module

let empty (interfaces : (Name.t * string) list)
  (module_name : CoqName.t option) : 'a t = {
  values = PathName.Map.empty;
  modules = PathName.Map.empty;
  active_module = FullMod.empty module_name [];
  load_module =
    (fun _ _ -> failwith "Cannot load module: no module loader specified.");
  run_in_external = (fun _ _ -> failwith "No external environment to run in.");
  convert = (fun _ -> failwith "Cannot convert: unknown destination type.");
  required_modules = ref Name.Set.empty;
  interfaces
}

(** Execute a function on another environment [env] if it is not the same as
    the current environment [env'].
    This ensures that we don't get into a situation where we are executing the
    same function repeatedly on the same arguments, expecting a different
    result. *)
let run_in_env (f : 'a t -> 'b * 'a t) (env' : 'a t) (env : 'a t)
  : 'b option * 'a t =
  if env == env' then
    (None, env)
  else
    let (x, env) = f env in
    (Some x, env)

let import_content (env : 'a t) : 'a t =
  let f env = ((env.values, env.modules), env) in
  match env.run_in_external f env with
  | Some (values, modules) ->
    let values = PathName.Map.map (Mod.Value.map env.convert) values in
    { env with
      values = PathName.Map.union (fun _ a _ -> Some a) env.values values;
      modules = PathName.Map.union (fun _ a _ -> Some a) env.modules modules;
    }
  | None -> env

let module_required (module_name : Name.t) (env : 'a t) : unit =
  env.required_modules := Name.Set.add module_name !(env.required_modules)

let requires (env : 'a t) : Name.t list =
  let rec f : 'b. 'b t -> Name.Set.t = fun env ->
    match env.run_in_external (fun env -> (f env, env)) env with
    | Some requires -> Name.Set.union !(env.required_modules) requires
    | None -> !(env.required_modules) in
  Name.Set.elements (f env)

let coq_path (env : 'a t) : Name.t list = FullMod.coq_path env.active_module

let update_active (f : Mod.t -> Mod.t) (env : 'a t) : 'a t =
  { env with active_module = FullMod.hd_mod_map f env.active_module }

let enter_module (module_name : CoqName.t) (env : 'a t) : 'a t =
  {env with active_module = FullMod.enter_module module_name env.active_module}

let enter_section (env : 'a t) : 'a t =
  {env with active_module = FullMod.enter_section env.active_module}

let localize (has_name : PathName.t -> Mod.t -> bool) (env : 'a t)
  (x : BoundName.t) : BoundName.t =
  FullMod.localize has_name env.active_module x

let has_value (env : 'a t) (x : PathName.t) (m : Mod.t) =
  let x = { x with PathName.path = m.Mod.coq_path @ x.PathName.path } in
  PathName.Map.mem x env.values

let has_global_value (env : 'a t) (x : PathName.t) =
  PathName.Map.mem x env.values

let localize_effects (env : 'a t) (typ : Effect.t) : Effect.t =
  Effect.map (localize (has_value env) env) typ

let combine (env1 : 'a t) (env2 : 'a t) : 'a t =
  env1.required_modules := Name.Set.union !(env1.required_modules)
    !(env2.required_modules);
  { env1 with
    values = PathName.Map.union (fun _ _ x -> Some x) env1.values env2.values;
    modules = PathName.Map.union (fun _ _ x -> Some x) env1.modules
      env2.modules;
    active_module = FullMod.combine env1.active_module env2.active_module;
  }

let bound_name_opt (find : PathName.t -> Mod.t -> PathName.t option)
  (has_name : PathName.t -> Mod.t -> bool) (x : PathName.t) (env : 'a t)
  : BoundName.t option =
  match FullMod.bound_name_opt find x env.active_module with
  | Some name -> Some (localize has_name env name)
  | None ->
    let f env =
      match FullMod.bound_name_opt find x env.active_module with
      | Some name -> (Some name, env)
      | None ->
        let module_name = match x with
          | { PathName.path = module_name :: _ } -> module_name
          | { PathName.path = []; base = module_name } -> module_name in
        let env = combine env @@ env.load_module module_name env in
        (FullMod.bound_name_opt find x env.active_module, env) in
    match env.run_in_external f env with
    | Some (Some name) -> Some (localize has_name env name)
    | Some None -> None
    | None -> failwith "Didn't attempt to search for an external module"

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
    run_in_external = (fun f _ -> env.run_in_external f (empty [] None));
    convert = (fun x -> f @@ env.convert x);
    }

let import_module (f : PathName.t -> PathName.t) (g : 'a t -> 'a -> 'a)
  (m : Mod.t) (env : 'a t) : Mod.t * 'a t =
  let env = env |> Mod.fold_modules (fun _ x env ->
    let m' = PathName.Map.find x env.modules in
    { env with
      modules = PathName.Map.add (f x) (Mod.map f m') env.modules
    }) m in
  let env = env |> Mod.fold_values (fun _ x env ->
    let v = PathName.Map.find x env.values in
    { env with
      values = PathName.Map.add (f x) v env.values
    }) m in
  let m = Mod.map f m in
  let env = env |> Mod.fold_values (fun _ x env ->
    let v = PathName.Map.find x env.values in
    { env with
      values = PathName.Map.add x (Mod.Value.map (g env) v) env.values
    }) m in
  (m, env)

let include_module (f : (PathName.t -> PathName.t) -> 'a t -> 'a -> 'a)
  (m : Mod.t) (env : 'a t) : 'a t =
  let module_path = m.Mod.coq_path in
  let env_path = coq_path env in
  let change_prefix name =
    match strip_prefix module_path name.PathName.path with
    | Some suffix -> { name with PathName.path = env_path @ suffix }
    | None -> name in
  let env = import_content env in
  let (m, env) = import_module change_prefix (f change_prefix) m env in
  { env with active_module = FullMod.include_module m env.active_module }

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
  let rec f : 'b. 'b t -> 'b Mod.Value.t = fun env ->
    match PathName.Map.find_opt x.full_path env.values with
    | Some v -> v
    | None ->
      match env.run_in_external (fun env -> (f env, env)) env with
      | Some v -> Mod.Value.map env.convert v
      | _ ->
        let message = BoundName.pp x ^^ !^ "not found." in
        Error.raise loc (SmartPrint.to_string 80 2 message) in
  f env

module Carrier (M : Mod.Carrier) = struct
  let resolve (path : Name.t list) (base : Name.t) (env : 'a t) : PathName.t =
    let x = PathName.of_name path base in
    match FullMod.hd_map (M.resolve_opt x) env.active_module with
    | Some path -> path
    | None -> find_free_path x env

  let localize (env : 'a t) (path : Name.t list) (base : Name.t) : BoundName.t =
    let x = PathName.of_name path base in
    let x = { BoundName.full_path = x; local_path = x } in
    FullMod.localize (has_value env) env.active_module x

  let coq_name (base : Name.t) (env : 'a t) : CoqName.t =
    CoqName.of_names base (resolve [] base env).PathName.base

  let bound_opt (x : PathName.t) (env : 'a t) : BoundName.t option =
    bound_name_opt M.resolve_opt (has_value env) x env

  let bound (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
    bound_name M.resolve_opt (has_value env) loc x env
end

module ValueCarrier (M : Mod.ValueCarrier) = struct
  include Carrier(M)
  let raw_add (x : PathName.t) (y : PathName.t) (v : 'a) (env : 'a t) : 'a t =
    { env with
      values = PathName.Map.add y (M.value v) env.values;
      active_module = FullMod.hd_mod_map (M.assoc x y) env.active_module }

  let add (path : Name.t list) (base : Name.t) (v : 'a) (env : 'a t) : 'a t =
    raw_add (PathName.of_name path base) (resolve path base env) v env

  let assoc (name : CoqName.t) (v : 'a) (env : 'a t) : 'a t =
    let (ocaml_name, coq_name) = CoqName.assoc_names name in
    raw_add (PathName.of_name [] ocaml_name)
      (PathName.of_name (coq_path env) coq_name) v env

  let find (loc : Loc.t) (x : BoundName.t) (env : 'a t) : 'a =
    M.unpack @@ find loc x env

  (** Add a fresh local name beginning with [prefix] in [env]. *)
  let fresh (prefix : string) (v : 'a) (env : 'a t)
    : CoqName.t * BoundName.t * 'a t =
    let name = find_free_name [] prefix env in
    let bound_name = {
      BoundName.full_path = { PathName.path = coq_path env; base = name };
      local_path = { PathName.path = []; base = name };
    } in
    (CoqName.Name name, bound_name, add [] name v env)

  let create (prefix : Name.t) (v : 'a) (env : 'a t)
    : CoqName.t * BoundName.t * 'a t =
    let name = find_free_name [] prefix env in
    let bound_name = {
      BoundName.full_path = { PathName.path = coq_path env; base = name };
      local_path = { PathName.path = []; base = name };
    } in
    let coq_name = CoqName.of_names prefix name in
    (coq_name, bound_name, assoc coq_name v env)
end

module Var = ValueCarrier(Mod.Vars)

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

  let assoc (name : CoqName.t) (v : 'a) (typ : Effect.PureType.t)
    (env : 'a t) : 'a t =
    let (ocaml_name, coq_name) = CoqName.assoc_names name in
    raw_add (PathName.of_name [] ocaml_name)
      (PathName.of_name (coq_path env) coq_name) v typ env

  let find (loc : Loc.t) (x : BoundName.t) (env : 'a t)
    : Effect.PureType.t option =
    Mod.Function.unpack @@ find loc x env

  (** Add a fresh local name beginning with [prefix] in [env]. *)
  let fresh (prefix : string) (v : 'a) (typ : Effect.PureType.t) (env : 'a t)
    : CoqName.t * BoundName.t * 'a t =
    let name = find_free_name [] prefix env in
    let bound_name = {
      BoundName.full_path = { PathName.path = coq_path env; base = name };
      local_path = { PathName.path = []; base = name };
    } in
    (CoqName.Name name, bound_name, add [] name v typ env)

  let create (prefix : string) (v : 'a) (typ : Effect.PureType.t) (env : 'a t)
    : CoqName.t * BoundName.t * 'a t =
    let name = find_free_name [] prefix env in
    let bound_name = {
      BoundName.full_path = { PathName.path = coq_path env; base = name };
      local_path = { PathName.path = []; base = name };
    } in
    let coq_name = CoqName.of_names prefix name in
    (coq_name, bound_name, assoc coq_name v typ env)
end

module EmptyCarrier (M : Mod.EmptyCarrier) = struct
  include Carrier(M)
  let raw_add (x : PathName.t) (y : PathName.t) (env : 'a t) : 'a t =
    { env with
      values = PathName.Map.add y M.value env.values;
      active_module = FullMod.hd_mod_map (M.assoc x y) env.active_module }

  let add (path : Name.t list) (base : Name.t) (env : 'a t) : 'a t =
    raw_add (PathName.of_name path base) (resolve path base env) env

  let assoc (name : CoqName.t) (env : 'a t) : 'a t =
    let (ocaml_name, coq_name) = CoqName.assoc_names name in
    raw_add (PathName.of_name [] ocaml_name)
      (PathName.of_name (coq_path env) coq_name) env

  (** Add a fresh local name beginning with [prefix] in [env]. *)
  let fresh (prefix : string) (env : 'a t) : CoqName.t * BoundName.t * 'a t =
    let name = find_free_name [] prefix env in
    let bound_name = {
      BoundName.full_path = { PathName.path = coq_path env; base = name };
      local_path = { PathName.path = []; base = name };
    } in
    (CoqName.Name name, bound_name, add [] name env)

  let create (prefix : string) (env : 'a t) : CoqName.t * BoundName.t * 'a t =
    let name = find_free_name [] prefix env in
    let bound_name = {
      BoundName.full_path = { PathName.path = coq_path env; base = name };
      local_path = { PathName.path = []; base = name };
    } in
    let coq_name = CoqName.of_names prefix name in
    (coq_name, bound_name, assoc coq_name env)
end

module Typ = EmptyCarrier(Mod.Typs)
module Descriptor = EmptyCarrier(Mod.Descriptors)
module Constructor = EmptyCarrier(Mod.Constructors)

module Field = struct
  include Carrier(Mod.Fields)
  let raw_add (x : PathName.t) (y : PathName.t) (typ : Effect.PureType.t)
    (env : 'a t) : 'a t =
    { env with
      values = PathName.Map.add y (Mod.Fields.value typ) env.values;
      active_module =
        FullMod.hd_mod_map (Mod.Fields.assoc x y) env.active_module }

  let add (path : Name.t list) (base : Name.t) (typ : Effect.PureType.t)
    (env : 'a t) : 'a t =
    raw_add (PathName.of_name path base) (resolve path base env) typ env

  let assoc (name : CoqName.t) (typ : Effect.PureType.t) (env : 'a t) : 'a t =
    let (ocaml_name, coq_name) = CoqName.assoc_names name in
    raw_add (PathName.of_name [] ocaml_name)
      (PathName.of_name (coq_path env) coq_name) typ env

  (** Add a fresh local name beginning with [prefix] in [env]. *)
  let fresh (prefix : string) (typ : Effect.PureType.t) (env : 'a t)
    : CoqName.t * BoundName.t * 'a t =
    let name = find_free_name [] prefix env in
    let bound_name = {
      BoundName.full_path = { PathName.path = coq_path env; base = name };
      local_path = { PathName.path = []; base = name };
    } in
    (CoqName.Name name, bound_name, add [] name typ env)

  let create (prefix : string) (typ : Effect.PureType.t) (env : 'a t)
    : CoqName.t * BoundName.t * 'a t =
    let name = find_free_name [] prefix env in
    let bound_name = {
      BoundName.full_path = { PathName.path = coq_path env; base = name };
      local_path = { PathName.path = []; base = name };
    } in
    let coq_name = CoqName.of_names prefix name in
    (coq_name, bound_name, assoc coq_name typ env)
end

module Exception = struct
  include EmptyCarrier(Mod.Descriptors)

  let raw_add (x : PathName.t) (y : PathName.t) (raise_name : PathName.t)
    (env : 'a t) : 'a t =
    { env with
      values = PathName.Map.add y (Mod.Exception.value raise_name) env.values;
      active_module = FullMod.hd_mod_map (Mod.Exception.assoc x y)
        env.active_module }

  let add (path : Name.t list) (base : Name.t) (raise_name : PathName.t)
    (env : 'a t) : 'a t =
    raw_add (PathName.of_name path base) (resolve path base env) raise_name env

  let assoc (name : CoqName.t) (raise_name : PathName.t) (env : 'a t) : 'a t =
    let (ocaml_name, coq_name) = CoqName.assoc_names name in
    raw_add (PathName.of_name [] ocaml_name)
      (PathName.of_name (coq_path env) coq_name) raise_name env

  let find (loc : Loc.t) (x : BoundName.t) (env : 'a t) : PathName.t =
    Mod.Exception.unpack @@ find loc x env

  (** Add a fresh local name beginning with [prefix] in [env]. *)
  let fresh (prefix : string) (raise_name : PathName.t) (env : 'a t)
    : CoqName.t * BoundName.t * 'a t =
    let name = find_free_name [] prefix env in
    let bound_name = {
      BoundName.full_path = { PathName.path = coq_path env; base = name };
      local_path = { PathName.path = []; base = name };
    } in
    (CoqName.Name name, bound_name, add [] name raise_name env)
end

module Module = struct
  let resolve (path : Name.t list) (base : Name.t) (env : 'a t) : PathName.t =
    let x = PathName.of_name path base in
    match FullMod.hd_map (Mod.Modules.resolve_opt x) env.active_module with
    | Some path -> path
    | None -> { path = coq_path env @ x.path; base = x.base }

  let has_name (env : 'a t) (x : PathName.t) (m : Mod.t) =
    let x = { x with PathName.path = m.Mod.coq_path @ x.PathName.path } in
    PathName.Map.mem x env.modules

  let localize (env : 'a t) (path : Name.t list) (base : Name.t) : BoundName.t =
    let x = PathName.of_name path base in
    let x = { BoundName.full_path = x; local_path = x } in
    FullMod.localize (has_name env) env.active_module x

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

  let assoc (name : CoqName.t) (v : Mod.t) (env : 'a t) : 'a t =
    let (ocaml_name, coq_name) = CoqName.assoc_names name in
    raw_add (PathName.of_name [] ocaml_name)
      (PathName.of_name (coq_path env) coq_name) v env

  let find (loc : Loc.t) (x : BoundName.t) (env : 'a t) : Mod.t =
    let rec f : 'b. 'b t -> Mod.t = fun env ->
      match PathName.Map.find_opt x.full_path env.modules with
      | Some m -> m
      | None ->
        match env.run_in_external (fun env -> (f env, env)) env with
        | Some m -> m
        | _ ->
          let message = !^ "Module" ^^ BoundName.pp x ^^ !^ "not found." in
          Error.raise loc (SmartPrint.to_string 80 2 message) in
    f env

  (** Add a fresh local name beginning with [prefix] in [env]. *)
  let fresh (prefix : string) (v : Mod.t) (env : 'a t)
    : CoqName.t * BoundName.t * 'a t =
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
    let bound_name = {
      BoundName.full_path = { PathName.path = coq_path env; base = name };
      local_path = { PathName.path = []; base = name };
    } in
    (CoqName.Name name, bound_name, add [] name v env)

  let create (prefix : string) (v : Mod.t) (env : 'a t)
    : CoqName.t * BoundName.t * 'a t =
    let name = find_free_name [] prefix env in
    let bound_name = {
      BoundName.full_path = { PathName.path = coq_path env; base = name };
      local_path = { PathName.path = []; base = name };
    } in
    let coq_name = CoqName.of_names prefix name in
    (coq_name, bound_name, assoc coq_name v env)
end

let open_module (loc : Loc.t) (module_name : BoundName.t) (env : 'a t) : 'a t =
  let m = Module.find loc module_name env in
  { env with active_module = FullMod.open_module m env.active_module }

let open_module' (loc : Loc.t) (module_name : Name.t list) (env : 'a t) : 'a t =
  let path = PathName.of_name_list module_name in
  open_module loc (Module.bound loc path env) env

let leave_module (localize : 'a t -> 'a -> 'a) (env : 'a t) : 'a t =
  let (m, active_module) = FullMod.leave_module env.active_module in
  let env = { env with active_module } in
  let values = Mod.fold_values (fun _ x -> PathName.Map.update x
      (option_map (Mod.Value.map (localize env))))
    m env.values in
  let env = { env with active_module; values } in
  let module_name = match option_map CoqName.ocaml_name m.Mod.name with
    | Some module_name -> module_name
    | None -> failwith "Leaving a module with no name." in
  Module.raw_add (PathName.of_name [] module_name)
    (PathName.of_name_list m.coq_path) m env

let leave_signature (env : 'a t) : 'a t =
  let (m, active_module) = FullMod.leave_module env.active_module in
  let env = { env with active_module } in
  let module_name = match option_map CoqName.ocaml_name m.Mod.name with
    | Some module_name -> module_name
    | None -> failwith "Leaving a module signature with no name." in
  Module.raw_add (PathName.of_name [] module_name)
    (PathName.of_name_list m.coq_path) m env

let add_exception (path : Name.t list) (base : Name.t) (env : unit t) : unit t =
  let raise_path = {PathName.path = coq_path env @ path;
    base = "raise_" ^ base} in
  env
  |> Exception.add path base raise_path
  |> Var.add path ("raise_" ^ base) ()

let add_exception_with_effects (path : Name.t list) (base : Name.t)
  (env : Effect.t t) : Effect.t t =
  let raise_path = {PathName.path = coq_path env @ path;
    base = "raise_" ^ base} in
  let env = Exception.add path base raise_path env in
  let descriptor = PathName.of_name path base in
  let bound_descriptor = Descriptor.bound Loc.Unknown descriptor env in
  let effect =
    Effect.eff @@ Effect.Type.Arrow (
      Effect.Descriptor.singleton bound_descriptor [],
      Effect.Type.Pure) in
  Var.add path ("raise_" ^ base) effect env
