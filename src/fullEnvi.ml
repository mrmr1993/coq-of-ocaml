open SmartPrint
open Kerneltypes
open Utils

module Value = struct
  type 'a t =
    | Variable of 'a
    | Function of 'a * Effect.t
    | Type of Effect.Descriptor.t Kerneltypes.TypeDefinition.t'
    | Descriptor
    | Exception of PathName.t
    | Constructor of PathName.t * int
    | Field of PathName.t * int

  let map (f : 'a -> 'b) (v : 'a t) : 'b t =
    match v with
    | Variable a -> Variable (f a)
    | Function (a, typ) -> Function (f a, typ)
    | Type def -> Type def
    | Descriptor -> Descriptor
    | Exception raise_name -> Exception raise_name
    | Constructor (typ, index) -> Constructor (typ, index)
    | Field (typ, index) -> Field (typ, index)

  let to_string (v : 'a t) : string =
    match v with
    | Variable _ -> "variable"
    | Function _ -> "function"
    | Type _ -> "type"
    | Descriptor -> "descriptor"
    | Exception _ -> "exception"
    | Constructor _ -> "constructor"
    | Field _ -> "field"
end

type 'a t = {
  values : 'a Value.t PathName.Map.t;
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
    let values = PathName.Map.map (Value.map env.convert) values in
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
    values = PathName.Map.map (Value.map f) env.values;
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
      values = PathName.Map.add x (Value.map (g env) v) env.values
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

let find (loc : Loc.t) (x : BoundName.t) (env : 'a t) : 'a Value.t =
  let rec f : 'b. 'b t -> 'b Value.t = fun env ->
    match PathName.Map.find_opt x.full_path env.values with
    | Some v -> v
    | None ->
      match env.run_in_external (fun env -> (f env, env)) env with
      | Some v -> Value.map env.convert v
      | _ ->
        let message = BoundName.pp x ^^ !^ "not found." in
        Error.raise loc (SmartPrint.to_string 80 2 message) in
  f env

module type Carrier = sig
  val resolve_opt : PathName.t -> Mod.t -> PathName.t option
  val assoc : PathName.t -> PathName.t -> Mod.t -> Mod.t
  type 'a t
  type 'a t'
  val value : 'a t -> 'a Value.t
  val unpack : 'a Value.t -> 'a t'
end

module ValueCarrier (M : Carrier) = struct
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

  let raw_add (x : PathName.t) (y : PathName.t) (v : 'a M.t) (env : 'a t)
    : 'a t =
    { env with
      values = PathName.Map.add y (M.value v) env.values;
      active_module = FullMod.hd_mod_map (M.assoc x y) env.active_module }

  let add (path : Name.t list) (base : Name.t) (v : 'a M.t) (env : 'a t)
    : 'a t =
    raw_add (PathName.of_name path base) (resolve path base env) v env

  let assoc (name : CoqName.t) (v : 'a M.t) (env : 'a t) : 'a t =
    let (ocaml_name, coq_name) = CoqName.assoc_names name in
    raw_add (PathName.of_name [] ocaml_name)
      (PathName.of_name (coq_path env) coq_name) v env

  let find (loc : Loc.t) (x : BoundName.t) (env : 'a t) : 'a M.t' =
    M.unpack @@ find loc x env

  (** Add a fresh local name beginning with [prefix] in [env]. *)
  let fresh (prefix : string) (v : 'a M.t) (env : 'a t)
    : CoqName.t * BoundName.t * 'a t =
    let name = find_free_name [] prefix env in
    let bound_name = {
      BoundName.full_path = { PathName.path = coq_path env; base = name };
      local_path = { PathName.path = []; base = name };
    } in
    (CoqName.Name name, bound_name, add [] name v env)

  let create (prefix : Name.t) (v : 'a M.t) (env : 'a t)
    : CoqName.t * BoundName.t * 'a t =
    let name = find_free_name [] prefix env in
    let bound_name = {
      BoundName.full_path = { PathName.path = coq_path env; base = name };
      local_path = { PathName.path = []; base = name };
    } in
    let coq_name = CoqName.of_names prefix name in
    (coq_name, bound_name, assoc coq_name v env)
end

module Var = ValueCarrier(struct
  let resolve_opt (x : PathName.t) (m : Mod.t) : PathName.t option =
    PathName.Map.find_opt x m.Mod.vars

  let assoc (x : PathName.t) (y : PathName.t) (m : Mod.t) : Mod.t =
    { m with Mod.vars = PathName.Map.add x y m.Mod.vars }

  type 'a t = 'a
  type 'a t' = 'a

  let value (v : 'a) : 'a Value.t = Variable v

  let unpack (v : 'a Value.t) : 'a =
    match v with
    | Variable a -> a
    | Function (a, _) -> a
    | _ -> failwith @@ "Could not interpret " ^ Value.to_string v ^ " as a variable."
end)

module Function = ValueCarrier(struct
  let resolve_opt (x : PathName.t) (m : Mod.t) : PathName.t option =
    PathName.Map.find_opt x m.Mod.vars

  let assoc (x : PathName.t) (y : PathName.t) (m : Mod.t) : Mod.t =
    { m with Mod.vars = PathName.Map.add x y m.Mod.vars }

  type 'a t = 'a * Effect.t
  type 'a t' = Effect.t option

  let value ((v, typ) : 'a * Effect.t) : 'a Value.t = Function (v, typ)

  let unpack (v : 'a Value.t) : Effect.t option =
    match v with
    | Variable _ -> None
    | Function (_, typ) -> Some typ
    | _ -> failwith @@ "Could not interpret " ^ Value.to_string v ^ " as a variable."
end)

module Typ = ValueCarrier(struct
  let resolve_opt (x : PathName.t) (m : Mod.t) : PathName.t option =
    PathName.Map.find_opt x m.Mod.typs

  let assoc (x : PathName.t) (y : PathName.t) (m : Mod.t) : Mod.t =
    { m with Mod.typs = PathName.Map.add x y m.Mod.typs }

  type 'a t = Effect.Descriptor.t Kerneltypes.TypeDefinition.t'
  type 'a t' = Effect.Descriptor.t Kerneltypes.TypeDefinition.t'

  let value (def : 'a t) : 'a Value.t = Type def

  let unpack (v : 'a Value.t) : 'a t' =
    match v with
    | Type def -> def
    | _ -> failwith @@ "Could not interpret " ^ Value.to_string v ^ " as a type."
end)

module Descriptor = ValueCarrier(struct
  let resolve_opt (x : PathName.t) (m : Mod.t) : PathName.t option =
    PathName.Map.find_opt x m.Mod.descriptors

  let assoc (x : PathName.t) (y : PathName.t) (m : Mod.t) : Mod.t =
    { m with Mod.descriptors = PathName.Map.add x y m.Mod.descriptors }

  type 'a t = unit
  type 'a t' = unit

  let value () : 'a Value.t = Descriptor

  let unpack (v : 'a Value.t) : 'a t' = ()
end)

module Exception = ValueCarrier(struct
  let resolve_opt (x : PathName.t) (m : Mod.t) : PathName.t option =
    PathName.Map.find_opt x m.Mod.descriptors

  let assoc (x : PathName.t) (y : PathName.t) (m : Mod.t) : Mod.t =
    { m with Mod.descriptors = PathName.Map.add x y m.Mod.descriptors }

  type 'a t = PathName.t
  type 'a t' = PathName.t

  let value (raise_name : PathName.t) : 'a Value.t = Exception raise_name

  let unpack (v : 'a Value.t) : PathName.t =
    match v with
    | Exception raise_name -> raise_name
    | _ -> failwith @@ "Could not interpret " ^ Value.to_string v ^ " as an exception."
end)

module Constructor = ValueCarrier(struct
  let resolve_opt (x : PathName.t) (m : Mod.t) : PathName.t option =
    PathName.Map.find_opt x m.Mod.constructors

  let assoc (x : PathName.t) (y : PathName.t) (m : Mod.t) : Mod.t =
    { m with Mod.constructors = PathName.Map.add x y m.Mod.constructors }

  type 'a t = PathName.t * int
  type 'a t' = PathName.t * int

  let value ((typ, index) : PathName.t * int) : 'a Value.t =
    Constructor (typ, index)

  let unpack (v : 'a Value.t) : PathName.t * int =
    match v with
    | Constructor (typ, index) -> (typ, index)
    | _ -> failwith @@ "Could not interpret " ^ Value.to_string v ^ " as a constructor."
end)

module Field = ValueCarrier(struct
  let resolve_opt (x : PathName.t) (m : Mod.t) : PathName.t option =
    PathName.Map.find_opt x m.Mod.fields

  let assoc (x : PathName.t) (y : PathName.t) (m : Mod.t) : Mod.t =
    { m with Mod.fields = PathName.Map.add x y m.Mod.fields }

  type 'a t = PathName.t * int
  type 'a t' = PathName.t * int

  let value ((typ, index) : PathName.t * int) : 'a Value.t =
    Field (typ, index)

  let unpack (v : 'a Value.t) : PathName.t * int =
    match v with
    | Field (typ, index) -> (typ, index)
    | _ -> failwith @@ "Could not interpret " ^ Value.to_string v ^ " as a field."
end)

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
      (option_map (Value.map (localize env))))
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
    Effect.eff @@ Effect.Type.Arrow (Effect.Type.pure, Effect.Type.Monad (
      Effect.Descriptor.singleton bound_descriptor [],
      Effect.Type.pure)) in
  Var.add path ("raise_" ^ base) effect env
