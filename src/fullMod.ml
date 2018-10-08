open SmartPrint
open Utils

type t' =
  | Module of Mod.t
  | Include of Mod.t
  | Open of Mod.t

type t = t' list

let pp (env : t) : SmartPrint.t =
  env |> OCaml.list (fun m ->
    match m with
    | Module m -> Mod.pp m
    | Include m -> group (!^ "include" ^^ braces (Mod.pp m))
    | Open m ->
      group (!^ "open" ^^
        separate (!^ ".") @@ List.map Name.pp m.Mod.coq_path))

let empty (module_name : CoqName.t option) (coq_path : Name.t list) : t =
  [Module (Mod.empty module_name coq_path)]

let hd_map (f : Mod.t -> 'b) (env : t) : 'b =
  match env with
  | Module m :: env -> f m
  | (Include _ | Open _) :: env ->
    failwith "The head of the environment must be a module."
  | [] -> failwith "The environment must be a non-empty list."

let hd_mod_map (f : Mod.t -> Mod.t) (env : t) : t =
  match env with
  | Module m :: env -> Module (f m) :: env
  | (Include _ | Open _) :: env ->
    failwith "The head of the environment must be a module."
  | [] -> failwith "The environment must be a non-empty list."

let rec coq_path (env : t) : Name.t list = hd_map (fun m -> m.Mod.coq_path) env

let combine (env1 : t) (env2 : t) : t =
  List.map2 (fun m1 m2 ->
      match m1, m2 with
      | Module m1, Module m2 -> Module (Mod.combine m1 m2)
      | Include m1', Include m2' | Open m1', Open m2' ->
        if m1' == m2' then m1
        else failwith "Cannot combine incompatable environments."
      | _, _ -> failwith "Cannot combine incompatable environments.")
    env1 env2

let enter_module (module_name : CoqName.t) (env : t) : t =
  Module (Mod.empty (Some module_name) (coq_path env)) :: env

let enter_section (env : t) : t =
  Module (Mod.empty None (coq_path env)) :: env

let open_module (m : Mod.t) (env : t) : t =
  Module (Mod.empty None (coq_path env)) :: Open m :: env

let include_module (m : Mod.t) (env : t) : t =
  let m = { m with name = None; coq_path = coq_path env } in
  Module (Mod.empty None (coq_path env)) :: Include m :: env

let leave_module (env : t) : Mod.t * t =
  let rec leave_module_rec (env : t) =
    match env with
    | Module m1 :: (Module m2 | Include m2) :: env ->
      let m = Mod.finish_module m1 m2 in
      begin match m1.name with
      | Some _ -> (m1, Module m :: env)
      | None -> (* This is a partial module, continue to the rest of it. *)
        leave_module_rec (Module m :: env)
      end
    | Module m :: Open mo :: env ->
      leave_module_rec @@ Module m :: env
    | _ -> failwith "You should have entered in at least one module." in
  leave_module_rec env

let rec bound_name_opt (find : PathName.t -> Mod.t -> PathName.t option)
  (x : PathName.t) (env : t) : BoundName.t option =
  match env with
  | (Module m | Include m | Open m) :: env ->
    (match find x m with
    | Some name -> Some { BoundName.full_path = name; local_path = x }
    | None -> bound_name_opt find x env)
  | [] -> None

let bound_module_opt (x : PathName.t) (env : t) : BoundName.t option =
  bound_name_opt Mod.Modules.resolve_opt x env

let localize (has_name : PathName.t -> Mod.t -> bool) (env : t)
  (x : PathName.t) : PathName.t =
  let rec localize_name (path : Name.t list) (base : Name.t) (env : t)
      (env' : Mod.t list) =
    match env with
    | [] -> None
    | Module m :: env | Include m :: env | Open m :: env ->
      match strip_prefix m.Mod.coq_path path with
      | None -> localize_name path base env (m :: env')
      | Some path' ->
        let path_name = PathName.of_name path' base in
        if List.exists (has_name path_name) env' then
          localize_name path base env (m :: env')
        else
          Some path_name in
  match localize_name x.PathName.path x.PathName.base env [] with
  | Some name -> name
  | None -> x
