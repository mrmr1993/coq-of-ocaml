open SmartPrint
open Utils

type 'a t' =
  | Module of 'a Mod.t
  | Include of 'a Mod.t
  | Open of 'a Mod.t * int (* (module, depth) *)

type 'a t = 'a t' list

let pp (env : 'a t) : SmartPrint.t =
  env |> OCaml.list (fun m ->
    match m with
    | Module m -> Mod.pp m
    | Include m -> !^ "include" ^^ braces (Mod.pp m)
    | Open (m, _) ->
      !^ "open" ^^ separate (!^ ".") (List.map Name.pp m.Mod.coq_path))

let empty (module_name : CoqName.t option) (coq_path : Name.t list)
  : 'a t =
  [Module (Mod.empty module_name coq_path)]

let hd_map (f : 'a Mod.t -> 'b) (env : 'a t) : 'b =
  match env with
  | Module m :: env -> f m
  | (Include _ | Open _) :: env ->
    failwith "The head of the environment must be a module."
  | [] -> failwith "The environment must be a non-empty list."

let hd_mod_map (f : 'a Mod.t -> 'a Mod.t) (env : 'a t) : 'a t =
  match env with
  | Module m :: env -> Module (f m) :: env
  | (Include _ | Open _) :: env ->
    failwith "The head of the environment must be a module."
  | [] -> failwith "The environment must be a non-empty list."

let coq_path (env : 'a t) : Name.t list =
  hd_map (fun m -> m.Mod.coq_path) env

let enter_module (module_name : CoqName.t) (env : 'a t) : 'a t =
  Module (Mod.empty (Some module_name) (coq_path env)) :: env

let enter_section (env : 'a t) : 'a t =
  Module (Mod.empty None (coq_path env)) :: env

let open_module (m : 'a Mod.t) (depth : int) (env : 'a t) : 'a t =
  Module (Mod.empty None (coq_path env)) :: Open (m, depth) :: env

let include_module (m : 'a Mod.t) (env : 'a t) : 'a t =
  let m = { m with name = None; coq_path = coq_path env } in
  Module (Mod.empty None (coq_path env)) :: Include m :: env

let leave_module (prefix : Name.t option -> 'a -> 'a)
  (resolve_open : Name.t list -> 'a -> 'a) (localize : 'a t -> 'a -> 'a)
  (env : 'a t) : 'a t =
  let rec leave_module_rec (env : 'a t) =
    match env with
    | Module m1 :: (Module m2 | Include m2) :: env ->
      let m = Mod.finish_module prefix m1 m2 in
      begin match m1.name with
      | Some _ ->
        let env' = Module m :: env in
        Module (Mod.map_values (localize env') m) :: env
      | None -> (* This is a partial module, continue to the rest of it. *)
        leave_module_rec (Module m :: env)
      end
    | Module m :: Open (mo, depth) :: env ->
      leave_module_rec @@
        Module (Mod.map (resolve_open mo.Mod.coq_path) m) :: env
    | _ -> failwith "You should have entered in at least one module." in
  leave_module_rec env

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

let rec bound_name_opt (find : PathName.t -> 'a Mod.t -> PathName.t option)
  (x : PathName.t) (env : 'a t) : BoundName.t option =
  match env with
  | Module m :: env | Include m :: env ->
    begin match find x m with
    | Some x -> Some {
        BoundName.full_path =
          { x with PathName.path = m.Mod.coq_path @ x.path };
        local_path = x;
        path_name = x;
        depth = 0 }
    | None ->
      bound_name_opt find x env
        |> option_map (fun name ->
          { name with BoundName.depth = name.BoundName.depth + 1 })
    end
  | Open (m, depth) :: env ->
    (match find x m with
    | Some x ->
      let x = { x with PathName.path = m.Mod.coq_path @ x.PathName.path } in
      Some { BoundName.full_path = x; local_path = x; path_name = x; depth }
    | None -> bound_name_opt find x env)
      |> option_map (fun name ->
        { name with BoundName.depth = name.BoundName.depth + 1 })
  | [] -> None

let bound_module_opt (x : PathName.t) (env : 'a t) : BoundName.t option =
  bound_name_opt Mod.Modules.resolve_opt x env

let localize_opt (x : BoundName.t) (env : 'a t) : BoundName.t option =
  let rec has_resolved_name (x : PathName.t) (env : 'a Mod.t list) =
    match env with
    | [] -> false
    | m :: env ->
      if PathName.Map.mem x m.Mod.values then true
      else if PathName.Map.mem x m.Mod.modules then true
      else has_resolved_name x env in
  let rec localize_name (path : Name.t list) (base : Name.t) (env : 'a t)
      (env' : 'a Mod.t list) =
    match env with
    | [] -> None
    | Module m :: env | Include m :: env | Open (m, _) :: env ->
      match strip_prefix m.Mod.coq_path path with
      | None -> localize_name path base env (m :: env')
      | Some path' ->
        let path_name = PathName.of_name path' base in
        if not (has_resolved_name path_name [m]) ||
            has_resolved_name path_name env' then
          localize_name path base env (m :: env')
        else
          Some path_name in
  let full_path = x.BoundName.full_path in
  localize_name full_path.PathName.path full_path.PathName.base env []
  |> option_map (fun path -> { x with BoundName.local_path = path })

let localize (loc : Loc.t) (env : 'a t) (name : BoundName.t) : BoundName.t =
  match localize_opt name env with
  | Some name -> name
  | None ->
      let message = BoundName.pp name ^^ !^ "could not be localised." in
      Error.warn loc (SmartPrint.to_string 80 2 message);
      name

let localize_type (loc : Loc.t) (env : 'a t) (typ : Effect.Type.t)
  : Effect.Type.t =
  Effect.Type.map (localize loc env) typ

let rec map (f : 'a -> 'b) (env : 'a t) : 'b t =
  List.map (fun m ->
    match m with
    | Module m -> Module (Mod.map f m)
    | Include m -> Include (Mod.map f m)
    | Open (m, depth) -> Open (Mod.map f m, depth)) env
