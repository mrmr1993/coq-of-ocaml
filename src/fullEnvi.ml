open SmartPrint

module WrappedMod = struct
  type 'a t = {
    m : 'a Mod.t;
    ocaml_name : Name.t;
    coq_name : Name.t
  }

  let map (f : 'a -> 'b) (wmod : 'a t) : 'b t =
    {wmod with m = Mod.map f wmod.m}
end

type 'a t = {
  active_module : 'a FullMod.t;
  available_modules : 'a WrappedMod.t Name.Map.t
}

let pp (env : 'a t) : SmartPrint.t = FullMod.pp env.active_module

let empty : 'a t = {
  active_module = FullMod.empty;
  available_modules = Name.Map.empty
}

let add_var (path : Name.t list) (base : Name.t) (v : 'a) (env : 'a t)
  : 'a t =
  {env with active_module = FullMod.add_var path base v env.active_module}

let add_typ (path : Name.t list) (base : Name.t) (env : 'a t)
  : 'a t =
  {env with active_module = FullMod.add_typ path base env.active_module}

let add_descriptor (path : Name.t list) (base : Name.t) (env : 'a t)
  : 'a t =
  {env with active_module = FullMod.add_descriptor path base env.active_module}

let add_constructor (path : Name.t list) (base : Name.t) (env : 'a t)
  : 'a t =
  {env with active_module = FullMod.add_constructor path base env.active_module}

let add_field (path : Name.t list) (base : Name.t) (env : 'a t)
  : 'a t =
  {env with active_module = FullMod.add_field path base env.active_module}

let add_module (path : Name.t list) (base : Name.t) (v : 'a Mod.t) (env : 'a t)
  : 'a t =
  {env with active_module = FullMod.add_module path base v env.active_module}

let enter_module (env : 'a t) : 'a t =
  {env with active_module = FullMod.enter_module env.active_module}

let leave_module (module_name : Name.t) (prefix : Name.t -> 'a -> 'a)
  (env : 'a t) : 'a t =
  {env with active_module = FullMod.leave_module module_name prefix env.active_module}

let find_first (f : 'a -> 'b option) (l : 'a list) : 'b option =
  FullMod.find_first f l

let find_external_module_path (x : PathName.t) (env : 'a t)
  : 'a WrappedMod.t * PathName.t =
  match x.PathName.path with
  | [] -> failwith "Cannot look up the given path name in the available modules"
  | module_name :: module_path ->
    let external_module = Name.Map.find module_name env.available_modules in
    let x = { x with PathName.path = module_path } in
    (external_module, x)

let rec bound_name_opt (find : PathName.t -> 'a Mod.t -> bool)
  (x : PathName.t) (env : 'a t) : BoundName.t option =
  match FullMod.bound_name_opt find x env.active_module with
  | Some name -> Some name
  | None ->
    match List.find_opt (fun open_name ->
      let x = { x with PathName.path = open_name @ x.PathName.path } in
      let (external_module, x) = find_external_module_path x env in
      find x external_module.m) (FullMod.external_opens env.active_module) with
    | Some open_name ->
      let x = { x with PathName.path = open_name @ x.PathName.path } in
      Some { BoundName.path_name = x; BoundName.depth = -1 }
    | None -> None

let bound_name (find : PathName.t -> 'a Mod.t -> bool) (loc : Loc.t)
  (x : PathName.t) (env : 'a t) : BoundName.t =
  match bound_name_opt find x env with
  | Some name -> name
  | None ->
    let message = PathName.pp x ^^ !^ "not found." in
    Error.raise loc (SmartPrint.to_string 80 2 message)

let bound_var (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
  bound_name Mod.Vars.mem loc x env

let bound_typ (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
  bound_name Mod.Typs.mem loc x env

let bound_descriptor (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
  bound_name Mod.Descriptors.mem loc x env

let bound_constructor (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
  bound_name Mod.Constructors.mem loc x env

let bound_field (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
  bound_name Mod.Fields.mem loc x env

let bound_module (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
  bound_name Mod.Modules.mem loc x env

let open_module (module_name : PathName.t) (env : 'a t) : 'a t =
  let module_name_list = PathName.to_name_list module_name in
  let active_module = match
    FullMod.bound_name_opt Mod.Modules.mem module_name env.active_module with
  | Some _ -> FullMod.open_module module_name_list env.active_module
  | None -> FullMod.open_external_module module_name_list env.active_module in
  {env with active_module}

let open_module' (module_name : Name.t list) (env : 'a t) : 'a t =
  open_module (PathName.of_name_list module_name) env

let add_exception (path : Name.t list) (base : Name.t) (env : unit t) : unit t =
  {env with active_module = FullMod.add_exception path base env.active_module}

let add_exception_with_effects (path : Name.t list) (base : Name.t)
  (id : Effect.Descriptor.Id.t) (env : Effect.Type.t t)
  : Effect.Type.t t =
  {env with active_module = FullMod.add_exception_with_effects path base id env.active_module}

let rec find_bound_name (find : PathName.t -> 'a Mod.t -> 'b) (x : BoundName.t)
  (env : 'a t) (open_lift : 'b -> 'b) : 'b =
  if x.BoundName.depth == -1 then
    let (external_module, x) = find_external_module_path x.path_name env in
    find x external_module.m
  else
    FullMod.find_bound_name find x env.active_module open_lift

let find_var (x : BoundName.t) (env : 'a t) (open_lift : 'a -> 'a) : 'a =
  find_bound_name Mod.Vars.find x env open_lift

let find_module (x : BoundName.t) (env : 'a t)
  (open_lift : 'a Mod.t -> 'a Mod.t) : 'a Mod.t =
  find_bound_name Mod.Modules.find x env open_lift

let fresh_var  (prefix : string) (v : 'a) (env : 'a t) : Name.t * 'a t =
  let (name, active_mod) = FullMod.fresh_var prefix v env.active_module in
  (name, {env with active_module = active_mod})

let map (f : 'a -> 'b) (env : 'a t) : 'b t =
  {active_module = FullMod.map f env.active_module;
   available_modules = Name.Map.map (WrappedMod.map f) env.available_modules}

let include_module (loc : Loc.t) (x : 'a Mod.t) (env : 'a t) : 'a t =
  {env with active_module = FullMod.include_module loc x env.active_module}
