open SmartPrint
open Utils

module WrappedMod = struct
  type 'a t = {
    m : 'a Mod.t;
    ocaml_name : Name.t;
    coq_name : Name.t
  }

  let pp (wmod : 'a t) : SmartPrint.t =
    OCaml.tuple [Name.pp wmod.ocaml_name; Name.pp wmod.coq_name; Mod.pp wmod.m]

  let map (f : 'a -> 'b) (wmod : 'a t) : 'b t =
    {wmod with m = Mod.map f wmod.m}
end


type 'a t = {
  active_module : 'a FullMod.t;
  get_module : Name.t -> 'a WrappedMod.t option;
  (* TODO: Move away from using a reference here by updating and passing env
     explicitly, possibly as a monad. *)
  required_modules : Name.Set.t ref
}

let pp (env : 'a t) : SmartPrint.t = FullMod.pp env.active_module

let empty (get_module : Name.t -> 'a WrappedMod.t option) : 'a t = {
  active_module = FullMod.empty;
  get_module;
  required_modules = ref Name.Set.empty
}

let module_required (module_name : Name.t) (env : 'a t) : unit =
  env.required_modules := Name.Set.add module_name !(env.required_modules)

let requires (env : 'a t) : Name.t list =
  Name.Set.elements !(env.required_modules)

let find_wrapped_mod_opt (module_name : Name.t) (env : 'a t)
  : 'a WrappedMod.t option =
  env.get_module module_name

let find_wrapped_mod (module_name : Name.t) (env : 'a t)
  : 'a WrappedMod.t =
  match find_wrapped_mod_opt module_name env with
  | Some wmod -> wmod
  | None -> failwith ("Could not find include " ^ Name.to_string module_name ^ ".")

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

let find_external_module_path_opt (x : PathName.t) (env : 'a t)
  : ('a WrappedMod.t * PathName.t) option =
  match x.PathName.path with
  | [] -> None
  | module_name :: module_path ->
    find_wrapped_mod_opt module_name env |>
      option_map (fun external_module ->
        let x = { x with PathName.path = module_path } in
        (external_module, x))

let find_external_module_path (x : PathName.t) (env : 'a t)
  : 'a WrappedMod.t * PathName.t =
  match find_external_module_path_opt x env with
  | Some ret -> ret
  | None ->
    failwith ("Could not find include for " ^ to_string 80 2 (PathName.pp x) ^ ".")

let bound_name_external_opt (find : PathName.t -> 'a Mod.t -> bool)
  (x : PathName.t) (env : 'a t) : BoundName.t option =
  find_first (fun open_name ->
    let x = { x with PathName.path = open_name @ x.PathName.path } in
    match find_external_module_path_opt x env with
    | Some (external_module, x) ->
      if find x external_module.m then
        let x = { x with path = external_module.coq_name :: x.path } in
        module_required external_module.coq_name env;
        Some { BoundName.path_name = x; BoundName.depth = -1 }
      else None
    | None -> None) (FullMod.external_opens env.active_module)

let bound_name_opt (find : PathName.t -> 'a Mod.t -> bool)
  (x : PathName.t) (env : 'a t) : BoundName.t option =
  match FullMod.bound_name_opt find x env.active_module with
  | Some name -> Some name
  | None -> bound_name_external_opt find x env

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

let bound_external_module_opt (x : PathName.t) (env : 'a t) : BoundName.t option =
  match x.path, find_wrapped_mod_opt x.base env with
  | [], Some {coq_name} -> (* This is a toplevel module *)
    module_required coq_name env;
    Some { BoundName.path_name = {PathName.path = []; PathName.base = coq_name};
      BoundName.depth = -1 }
  | _, _ -> None

let bound_external_module (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
  match bound_external_module_opt x env with
  | Some name -> name
  | None ->
      let message = PathName.pp x ^^ !^ "not found." in
      Error.raise loc (SmartPrint.to_string 80 2 message)

let bound_module_opt (x : PathName.t) (env : 'a t) : BoundName.t option =
  match bound_name_opt Mod.Modules.mem x env with
  | Some name -> Some name
  | None -> bound_external_module_opt x env

let bound_module (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
  match bound_module_opt x env with
  | Some name -> name
  | None ->
      let message = PathName.pp x ^^ !^ "not found." in
      Error.raise loc (SmartPrint.to_string 80 2 message)

let open_module_nocheck (module_name : PathName.t) (env : 'a t) : 'a t =
  let module_name_list = PathName.to_name_list module_name in
  {env with active_module = FullMod.open_module module_name_list env.active_module}

let open_module_struct (loc : Loc.t) (module_name : PathName.t) (env : 'a t)
  : PathName.t * 'a t =
  let (path_name, active_module) = match
      FullMod.bound_module_opt module_name env.active_module with
    | Some {BoundName.path_name} ->
      let module_name_list = PathName.to_name_list path_name in
      (path_name, FullMod.open_module module_name_list env.active_module)
    | None ->
      let {BoundName.path_name} = bound_external_module loc module_name env in
      let module_name_list = PathName.to_name_list path_name in
      (path_name, FullMod.open_external_module module_name_list env.active_module) in
  (path_name, {env with active_module})

let open_module (loc : Loc.t) (module_name : PathName.t) (env : 'a t) : 'a t =
  snd (open_module_struct loc module_name env)

let open_module' (loc : Loc.t) (module_name : Name.t list) (env : 'a t) : 'a t =
  open_module loc (PathName.of_name_list module_name) env

let add_exception (path : Name.t list) (base : Name.t) (env : unit t) : unit t =
  {env with active_module = FullMod.add_exception path base env.active_module}

let add_exception_with_effects (path : Name.t list) (base : Name.t)
  (id : Effect.Descriptor.Id.t) (env : Effect.Type.t t)
  : Effect.Type.t t =
  {env with active_module = FullMod.add_exception_with_effects path base id env.active_module}

let find_bound_name (find : PathName.t -> 'a Mod.t -> 'b) (x : BoundName.t)
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
  match x.path_name.path with
  | [] when x.BoundName.depth == -1 ->
    (* This is a reference to a top-level external module *)
    (find_wrapped_mod x.path_name.base env).m
  | _ -> find_bound_name Mod.Modules.find x env open_lift

let fresh_var  (prefix : string) (v : 'a) (env : 'a t) : Name.t * 'a t =
  let (name, active_mod) = FullMod.fresh_var prefix v env.active_module in
  (name, {env with active_module = active_mod})

let map (f : 'a -> 'b) (env : 'a t) : 'b t =
  {active_module = FullMod.map f env.active_module;
   get_module = (fun x -> option_map (WrappedMod.map f) (env.get_module x));
   required_modules = env.required_modules}

let include_module (loc : Loc.t) (x : 'a Mod.t) (env : 'a t) : 'a t =
  {env with active_module = FullMod.include_module loc x env.active_module}
