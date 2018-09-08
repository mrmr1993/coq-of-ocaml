open SmartPrint
open Utils

(* NOTE: This is designed under the assumption that
   - |ocaml_name| is a top-level name (ie. contains no '.' characters)
   - no two modules share the same |ocaml_name|
   - |coq_name| is some path name, followed by '.', followed by |ocaml_name| *)
let add_mod (wmod : 'a Mod.t) (env : 'a FullEnvi.t) : 'a FullEnvi.t =
  let (ocaml_name, coq_name) = CoqName.assoc_names @@ Mod.name wmod in
  { env with
    FullEnvi.loaded_modules = env.FullEnvi.loaded_modules
      |> Name.Map.add ocaml_name wmod
      |> Name.Map.add coq_name wmod
  }

let add_interface (env : Effect.Type.t FullEnvi.t) (coq_prefix : Name.t)
  (file_name : string) : Effect.Type.t Mod.t * Effect.Type.t FullEnvi.t =
  let interface = Interface.of_file file_name in
  let wmod = Interface.to_mod coq_prefix interface env in
  (wmod, add_mod wmod env)

(* Mutable list of Coq name, interface directory pairs. *)
let interfaces : (Name.t * string) list ref = ref []

let find_mod_opt (env : Effect.Type.t FullEnvi.t) (module_name : Name.t)
  : 'a Mod.t option * 'a FullEnvi.t =
  match Name.Map.find_opt module_name env.FullEnvi.loaded_modules with
  | Some wmod -> (Some wmod, env)
  | None ->
    let file_name = String.uncapitalize_ascii (Name.to_string module_name) in
    match find_first (fun (coq_prefix, dir) ->
        let file_name = Filename.concat dir (file_name ^ ".interface") in
        if Sys.file_exists file_name then Some (coq_prefix, file_name) else None)
      !interfaces with
    | Some (coq_prefix, file_name) ->
      let (wmod, env) = add_interface env coq_prefix file_name in
      (Some wmod, env)
    | None -> (None, env)
