open SmartPrint
open Utils

type 'a t = 'a Mod.t list

let pp (env : 'a t) : SmartPrint.t =
  OCaml.list Mod.pp env

let empty (module_name : CoqName.t) : 'a t = [Mod.empty module_name]

let hd_map (f : 'a Mod.t -> 'a t -> 'b) (env : 'a t) : 'b =
  match env with
  | m :: env -> f m env
  | [] -> failwith "The environment must be a non-empty list."

let hd_mod_map (f : 'a Mod.t -> 'a Mod.t) : 'a t -> 'a t =
  hd_map (fun m env -> f m :: env)

let enter_module (module_name : CoqName.t) (env : 'a t) : 'a t =
  Mod.empty module_name :: env

let rec external_opens (env : 'a t) : Name.t list list =
  match env with
  | m :: env -> m.external_opens @ external_opens env
  | [] -> []

let leave_module (prefix : Name.t -> 'a -> 'a) (env : 'a t) : 'a t =
  match env with
  | m1 :: m2 :: env ->
    let m = Mod.finish_module prefix m1 m2 in
    m :: env
  | _ -> failwith "You should have entered in at least one module."

let rec bound_name_opt (find : PathName.t -> 'a Mod.t -> PathName.t option)
  (x : PathName.t) (env : 'a t) : BoundName.t option =
  match env with
  | m :: env ->
    begin match find x m with
    | Some x -> Some { BoundName.path_name = x; BoundName.depth = 0 }
    | None ->
      m.Mod.opens |> find_first (fun path ->
        let x = { x with PathName.path = path @ x.PathName.path } in
        bound_name_opt find x env |> option_map (fun name ->
          { name with BoundName.depth = name.BoundName.depth + 1 }))
    end
  | [] -> None

let bound_module_opt (x : PathName.t) (env : 'a t) : BoundName.t option =
  bound_name_opt Mod.Modules.resolve_opt x env

let find_bound_name (find : PathName.t -> 'a Mod.t -> 'b) (x : BoundName.t)
  (env : 'a t) (open_lift : 'b -> 'b) : 'b =
  let m =
    try List.nth env x.BoundName.depth with
    | Failure _ -> raise Not_found in
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
    (name, m :: env)) env

let rec map (f : 'a -> 'b) (env : 'a t) : 'b t = List.map (Mod.map f) env
