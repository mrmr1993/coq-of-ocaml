open SmartPrint

type t = BoundName.t

let pp (o : t) : SmartPrint.t =
  nest (!^ "Open" ^^ BoundName.pp o)

let of_ocaml (env : 'a FullEnvi.t) (loc : Loc.t) (path : Path.t) : t =
  let path = PathName.of_path loc path in
  let bound_name = FullEnvi.bound_module loc path env in
  if bound_name.depth == -1 then
    let m = FullEnvi.find_module bound_name env (fun x -> x) in
    let (_, coq_name) = CoqName.assoc_names @@ Mod.name m in
    let path = match bound_name.path_name.path with
      | [] -> (* Toplevel module *)
        { PathName.path = []; base = coq_name }
      | external_module :: path ->
        { bound_name.path_name with path = coq_name :: path } in
    { bound_name with path_name = path }
  else bound_name

let update_env (loc : Loc.t) (o : t) (env : 'a FullEnvi.t) : 'a FullEnvi.t =
  FullEnvi.open_module o env

(** Pretty-print an open construct to Coq. *)
let to_coq (o : t): SmartPrint.t =
  nest (!^ "Import" ^^ BoundName.to_coq o ^-^ !^ ".")
