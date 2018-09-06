open SmartPrint
open Utils

type 'a t = {
  values : 'a Mod.Value.t PathName.Map.t;
  active_module : 'a FullMod.t;
  get_module : Name.t -> 'a Mod.t option;
  (* TODO: Move away from using a reference here by updating and passing env
     explicitly, possibly as a monad. *)
  required_modules : Name.Set.t ref
}

let pp (env : 'a t) : SmartPrint.t = FullMod.pp env.active_module

let empty (module_name : CoqName.t option)
  (get_module : Name.t -> 'a Mod.t option) : 'a t = {
  values = PathName.Map.empty;
  active_module = FullMod.empty module_name [];
  get_module;
  required_modules = ref Name.Set.empty
}

let module_required (module_name : Name.t) (env : 'a t) : unit =
  env.required_modules := Name.Set.add module_name !(env.required_modules)

let requires (env : 'a t) : Name.t list =
  Name.Set.elements !(env.required_modules)

let coq_path (env : 'a t) : Name.t list = FullMod.coq_path env.active_module

let find_mod_opt (module_name : Name.t) (env : 'a t) : 'a Mod.t option =
  env.get_module module_name

let find_mod (loc : Loc.t) (module_name : Name.t) (env : 'a t) : 'a Mod.t =
  match find_mod_opt module_name env with
  | Some wmod -> wmod
  | None -> Error.raise loc ("Could not find include " ^ Name.to_string module_name ^ ".")

let update_active (f : 'a Mod.t -> 'a Mod.t) (env : 'a t) : 'a t =
  { env with active_module = FullMod.hd_mod_map f env.active_module }

let enter_module (module_name : CoqName.t) (env : 'a t) : 'a t =
  {env with active_module = FullMod.enter_module module_name env.active_module}

let enter_section (env : 'a t) : 'a t =
  {env with active_module = FullMod.enter_section env.active_module}

let leave_module (prefix : 'a -> 'a) (resolve_open : 'a -> 'a)
  (localize : 'a FullMod.t -> 'a -> 'a) (env : 'a t) : 'a t =
  {env with active_module =
    FullMod.leave_module prefix resolve_open localize env.active_module}

let find_external_module_path_opt (x : PathName.t) (env : 'a t)
  : ('a Mod.t * PathName.t) option =
  match x.PathName.path with
  | [] -> None
  | module_name :: module_path ->
    find_mod_opt module_name env |>
      option_map (fun external_module ->
        let x = { x with PathName.path = module_path } in
        (external_module, x))

let find_external_module (x : PathName.t) (env : 'a t) : 'a Mod.t =
  match find_external_module_path_opt x env with
  | Some (external_module, _) -> external_module
  | None ->
    failwith @@ to_string 80 2 @@
      !^ "Could not find include for" ^^ PathName.pp x ^-^ !^ "."

let bound_name_external_opt (find : PathName.t -> 'a Mod.t -> PathName.t option)
  (x : PathName.t) (env : 'a t) : BoundName.t option =
  match find_external_module_path_opt x env with
  | Some (external_module, x) ->
    find x external_module |> option_map (fun (x : PathName.t) ->
      let (_, coq_name) = CoqName.assoc_names @@ Mod.name external_module in
      module_required coq_name env;
      { BoundName.full_path = x; local_path = x; depth = -1 })
  | None -> None

let localize (loc : Loc.t) (find : PathName.t -> 'a Mod.t -> PathName.t option)
  (x : BoundName.t) (env : 'a t) : BoundName.t =
  FullMod.localize loc find env.active_module x

let bound_name_opt (find : PathName.t -> 'a Mod.t -> PathName.t option)
  (x : PathName.t) (env : 'a t) : BoundName.t option =
  match FullMod.bound_name_opt find x env.active_module with
  | Some name -> Some (localize Loc.Unknown find name env)
  | None -> bound_name_external_opt find x env

let bound_name (find : PathName.t -> 'a Mod.t -> PathName.t option)
  (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
  match bound_name_opt find x env with
  | Some name -> name
  | None ->
    let message = PathName.pp x ^^ !^ "not found." in
    Error.raise loc (SmartPrint.to_string 80 2 message)

let bound_external_module_opt (x : PathName.t) (env : 'a t) : BoundName.t option =
  match x.path, find_mod_opt x.base env with
  | [], Some wmod -> (* This is a toplevel module *)
    let (_, coq_name) = CoqName.assoc_names @@ Mod.name wmod in
    module_required coq_name env;
    Some { BoundName.full_path = x; local_path = x; depth = -1 }
  | _, _ -> None

let find_bound_name (find : PathName.t -> 'a Mod.t -> 'b) (x : BoundName.t)
  (env : 'a t) (open_lift : 'b -> 'b) : 'b =
  if x.BoundName.depth == -1 then
    let external_module = find_external_module x.full_path env in
    find x.full_path external_module
  else
    FullMod.find_bound_name find x env.active_module open_lift

let map (f : 'a -> 'b) (env : 'a t) : 'b t =
  {values = PathName.Map.map (Mod.Value.map f) env.values;
   active_module = FullMod.map f env.active_module;
   get_module = (fun x -> option_map (Mod.map f) (env.get_module x));
   required_modules = env.required_modules}

let include_module (x : 'a Mod.t) (env : 'a t) : 'a t =
  { env with active_module = FullMod.include_module x env.active_module }

let find_free_name (path : Name.t list) (base_name : string) (env : 'a t)
  : Name.t =
  let values = FullMod.hd_map (fun m -> m.values) env.active_module in
  let prefix_n s n =
    if n = 0 then
      Name.of_string s
    else
      Name.of_string @@ Printf.sprintf "%s_%d" s n in
  let rec first_n (n : int) : Name.t =
    let name = prefix_n base_name n in
    if PathName.Map.mem (PathName.of_name path name) values then
      first_n (n + 1)
    else name in
  first_n 0

let find_free_path (x : PathName.t) (env : 'a t) : PathName.t =
  let path = coq_path env @ x.path in
  { PathName.path = path; base = find_free_name path x.base env }

module Carrier (M : Mod.Carrier) = struct
  let resolve (path : Name.t list) (base : Name.t) (env : 'a t) : PathName.t =
    let x = PathName.of_name path base in
    match FullMod.hd_map (M.resolve_opt x) env.active_module with
    | Some path -> path
    | None -> find_free_path x env

  let bound_opt (x : PathName.t) (env : 'a t) : BoundName.t option =
    bound_name_opt M.resolve_opt x env

  let bound (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
    bound_name M.resolve_opt loc x env
end

module ValueCarrier (M : Mod.ValueCarrier) = struct
  include Carrier(M)
  let raw_add (x : PathName.t) (y : PathName.t) (v : 'a) (env : 'a t) : 'a t =
    { env with
      values = PathName.Map.add y (M.value v) env.values;
      active_module = FullMod.hd_mod_map (M.assoc x y v) env.active_module }

  let add (path : Name.t list) (base : Name.t) (v : 'a) (env : 'a t) : 'a t =
    raw_add (PathName.of_name path base) (resolve path base env) v env

  let assoc (path : Name.t list) (base : Name.t) (assoc_base : Name.t) (v : 'a)
    (env : 'a t) : 'a t =
    raw_add (PathName.of_name path base)
      (PathName.of_name (coq_path env @ path) assoc_base) v env

  let find (x : BoundName.t) (env : 'a t) (open_lift : 'a -> 'a) : 'a =
    find_bound_name M.find x env open_lift

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
      active_module = FullMod.hd_mod_map (Mod.Function.assoc x y v typ)
        env.active_module }

  let add (path : Name.t list) (base : Name.t) (v : 'a)
    (typ : Effect.PureType.t) (env : 'a t) : 'a t =
    raw_add (PathName.of_name path base) (resolve path base env) v typ env

  let assoc (path : Name.t list) (base : Name.t) (assoc_base : Name.t) (v : 'a)
    (typ : Effect.PureType.t) (env : 'a t) : 'a t =
    raw_add (PathName.of_name path base)
      (PathName.of_name (coq_path env @ path) assoc_base) v typ env

  let find (x : BoundName.t) (env : 'a t)
    (open_lift : Effect.PureType.t -> Effect.PureType.t)
    : Effect.PureType.t option =
    find_bound_name Mod.Function.find x env (option_map open_lift)

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

  let bound_opt (x : PathName.t) (env : 'a t) : BoundName.t option =
    match bound_name_opt Mod.Modules.resolve_opt x env with
    | Some name -> Some name
    | None -> bound_external_module_opt x env

  let bound (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
    match bound_opt x env with
    | Some name -> name
    | None ->
        let message = PathName.pp x ^^ !^ "not found." in
        Error.raise loc (SmartPrint.to_string 80 2 message)

  let raw_add (x : PathName.t) (y : PathName.t) (v : 'a Mod.t) (env : 'a t)
    : 'a t =
    { env with
      active_module =
        FullMod.hd_mod_map (Mod.Modules.assoc x y v) env.active_module }

  let add (path : Name.t list) (base : Name.t) (v : 'a Mod.t) (env : 'a t)
    : 'a t =
    raw_add (PathName.of_name path base) (resolve path base env) v env

  let assoc (path : Name.t list) (base : Name.t) (assoc_base : Name.t)
    (v : 'a Mod.t) (env : 'a t) : 'a t =
    raw_add (PathName.of_name path base)
      (PathName.of_name (coq_path env @ path) assoc_base) v env

  let find (loc : Loc.t) (x : BoundName.t) (env : 'a t)
    (open_lift : 'a Mod.t -> 'a Mod.t) : 'a Mod.t =
    match x.full_path.path with
    | [] when x.BoundName.depth == -1 ->
      (* This is a reference to a top-level external module *)
      find_mod loc x.full_path.base env
    | _ -> find_bound_name Mod.Modules.find x env open_lift

  (** Add a fresh local name beginning with [prefix] in [env]. *)
  let fresh (prefix : string) (v : 'a Mod.t) (env : 'a t) : Name.t * 'a t =
    let path = coq_path env in
    let modules = FullMod.hd_map (fun m -> m.modules) env.active_module in
    let rec first_n (n : int) : Name.t =
      let name = if n = 0 then
          Name.of_string prefix
        else
          Name.of_string @@ Printf.sprintf "%s_%d" prefix n in
      if PathName.Map.mem (PathName.of_name path name) modules then
        first_n (n + 1)
      else name in
    let name = first_n 0 in
    (name, add [] name v env)
end

let open_module (loc : Loc.t) (module_name : BoundName.t) (env : 'a t) : 'a t =
  let m = Module.find loc module_name env (fun x -> x) in
  { env with active_module =
      FullMod.open_module m module_name.depth env.active_module }

let open_module' (loc : Loc.t) (module_name : Name.t list) (env : 'a t) : 'a t =
  let path = PathName.of_name_list module_name in
  open_module loc (Module.bound loc path env) env

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
