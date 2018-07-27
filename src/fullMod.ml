open SmartPrint
open Utils

type 'a t' =
  | Module of 'a Mod.t
  | Include of 'a Mod.t
  | Alias of PathName.t
  | ExternalAlias of PathName.t

type 'a t = 'a t' list

let pp (env : 'a t) : SmartPrint.t =
  env |> OCaml.list (fun m ->
    match m with
    | Module m -> Mod.pp m
    | Include m -> !^ "include" ^^ braces (Mod.pp m)
    | Alias name -> !^ "open" ^^ PathName.pp name
    | ExternalAlias name -> !^ "open (external)" ^^ PathName.pp name)

let empty (module_name : CoqName.t option) : 'a t =
  [Module (Mod.empty module_name)]

let hd_map (f : 'a Mod.t -> 'a t -> 'b) (env : 'a t) : 'b =
  match env with
  | Module m :: env -> f m env
  | (Include _ | Alias _ | ExternalAlias _) :: env ->
    failwith "The head of the environment must be a module."
  | [] -> failwith "The environment must be a non-empty list."

let hd_mod_map (f : 'a Mod.t -> 'a Mod.t) : 'a t -> 'a t =
  hd_map (fun m env -> Module (f m) :: env)

let enter_module (module_name : CoqName.t) (env : 'a t) : 'a t =
  Module (Mod.empty (Some module_name)) :: env

let enter_section (env : 'a t) : 'a t =
  Module (Mod.empty None) :: env

let open_module (module_name : PathName.t) (env : 'a t) : 'a t =
  Module (Mod.empty None) :: Alias module_name :: env

let open_external_module (module_name : PathName.t) (env : 'a t) : 'a t =
  Module (Mod.empty None) :: ExternalAlias module_name :: env

let include_module (m : 'a Mod.t) (env : 'a t) : 'a t =
  let m = { m with name = None } in
  Module (Mod.empty None) :: Include m :: env

let rec leave_module (prefix : Name.t option -> 'a -> 'a) (env : 'a t) : 'a t =
  match env with
  | Module m1 :: Module m2 :: env ->
    let m = Mod.finish_module prefix m1 m2 in
    begin match m1.name with
    | Some _ -> Module m :: env
    | None -> (* This is a partial module, continue to the rest of it. *)
      leave_module prefix (Module m :: env)
    end
  | Module m :: Include mi :: env ->
    leave_module prefix @@ Module (Mod.finish_module prefix m mi) :: env
  | Module m :: Alias path :: env ->
    leave_module prefix @@ Module (Mod.map (prefix None) m) :: env
  | Module m :: ExternalAlias path :: env ->
    leave_module prefix @@ Module (Mod.map (prefix None) m) :: env
  | _ -> failwith "You should have entered in at least one module."

let rec bound_name_opt (find : PathName.t -> 'a Mod.t -> PathName.t option)
  (external_module : Name.t list -> 'a Mod.t * Name.t list) (x : PathName.t)
  (env : 'a t) : BoundName.t option =
  match env with
  | Module m :: env | Include m :: env ->
    begin match find x m with
    | Some x -> Some { BoundName.path_name = x; BoundName.depth = 0 }
    | None ->
      bound_name_opt find external_module x env
        |> option_map (fun name ->
          { name with BoundName.depth = name.BoundName.depth + 1 })
    end
  | Alias module_path :: env ->
    [{ x with PathName.path = PathName.to_name_list module_path @ x.path }; x]
      |> find_first (fun x -> bound_name_opt find external_module x env)
      |> option_map (fun name ->
        { name with BoundName.depth = name.BoundName.depth + 1 })
  | ExternalAlias module_path :: env ->
    let module_path = PathName.to_name_list module_path in
    let (m, module_path) = external_module module_path in
    let x = { x with PathName.path = module_path @ x.path } in
    begin match find x m with
    | Some x ->
      let (_, coq_name) = CoqName.assoc_names @@ Mod.name m in
      let x = { x with path = coq_name :: x.path } in
      Some { BoundName.path_name = x; BoundName.depth = -1 }
    | None -> bound_name_opt find external_module x env
    end
  | [] -> None

let bound_module_opt (external_module : Name.t list -> 'a Mod.t * Name.t list)
  (x : PathName.t) (env : 'a t) : BoundName.t option =
  bound_name_opt Mod.Modules.resolve_opt external_module x env

let find_bound_name (find : PathName.t -> 'a Mod.t -> 'b) (x : BoundName.t)
  (env : 'a t) (open_lift : 'b -> 'b) : 'b =
  let m =
    try List.nth env x.BoundName.depth with
    | Failure _ -> raise Not_found in
  let m = match m with
    | Module m | Include m -> m
    | _ -> failwith "Invalid bound name." in
  let rec iterate_open_lift v n =
    if n = 0 then
      v
    else
      iterate_open_lift (open_lift v) (n - 1) in
  let v = find x.BoundName.path_name m in
  iterate_open_lift v x.BoundName.depth

let fresh_var  (prefix : string) (v : 'a) (env : 'a t) : Name.t * 'a t =
  hd_map (fun m env ->
    let (name, m) = Mod.Vars.fresh prefix v m in
    (name, Module m :: env)) env

let rec map (f : 'a -> 'b) (env : 'a t) : 'b t =
  List.map (fun m ->
    match m with
    | Module m -> Module (Mod.map f m)
    | Include m -> Include (Mod.map f m)
    | Alias path -> Alias path
    | ExternalAlias path -> ExternalAlias path) env
