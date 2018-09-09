open SmartPrint
open Utils

let load_interface (env : Effect.Type.t FullEnvi.t) (coq_prefix : Name.t)
  (file_name : string) : Name.t * Effect.Type.t FullEnvi.t =
  let interface = Interface.of_file file_name in
  Interface.load_interface coq_prefix interface env

(* Mutable list of Coq name, interface directory pairs. *)
let interfaces : (Name.t * string) list ref = ref []

let load_module (x : PathName.t) (env : Effect.Type.t FullEnvi.t)
  : 'a FullEnvi.t =
  let module_name = match x with
    | { PathName.path = module_name :: _ } -> module_name
    | { PathName.path = []; base = module_name } -> module_name in
  let module_path = { PathName.path = []; base = module_name } in
  match FullEnvi.Module.bound_opt module_path env with
  | Some _ -> env
  | None ->
    let file_name = String.uncapitalize_ascii (Name.to_string module_name) in
    match find_first (fun (coq_prefix, dir) ->
        let file_name = Filename.concat dir (file_name ^ ".interface") in
        if Sys.file_exists file_name then Some (coq_prefix, file_name) else None)
      !interfaces with
    | Some (coq_prefix, file_name) ->
      let (module_name, env) = load_interface env coq_prefix file_name in
      FullEnvi.module_required module_name env;
      env
    | None -> env
