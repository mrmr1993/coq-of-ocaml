open SmartPrint

type 'a t = 'a FullEnvi.WrappedMod.t Name.Map.t

let empty = Name.Map.empty

(* NOTE: This is designed under the assumption that
   - |ocaml_name| is a top-level name (ie. contains no '.' characters)
   - no two modules share the same |ocaml_name|
   - |coq_name| is some path name, followed by '.', followed by |ocaml_name| *)
let add_wrapped_mod (wmod : 'a FullEnvi.WrappedMod.t) (loader : 'a t) : 'a t =
  loader
  |> Name.Map.add wmod.ocaml_name wmod
  |> Name.Map.add wmod.coq_name wmod

let add_interface (env : Effect.Type.t FullEnvi.t) (coq_prefix : Name.t)
  (loader : Effect.Type.t t) (file_name : string)
  : Effect.Type.t FullEnvi.WrappedMod.t * Effect.Type.t t =
  let interface = Interface.of_file file_name in
  let wmod = Interface.to_wrapped_mod coq_prefix interface env in
  (wmod, add_wrapped_mod wmod loader)

let rec find_interfaces_dir (base : string) : string option =
  let base_path = Filename.dirname base in
  if base == base_path then
    None
  else
    let interfaces_dir = Filename.concat base_path "interfaces" in
    if Sys.file_exists interfaces_dir && Sys.is_directory interfaces_dir then
      Some interfaces_dir
    else
      find_interfaces_dir base_path

let find_wrapped_mod_opt (env : Effect.Type.t FullEnvi.t) (loader : 'a t)
  (module_name : Name.t) : 'a FullEnvi.WrappedMod.t option * 'a t =
  match Name.Map.find_opt module_name loader with
  | Some wmod -> (Some wmod, loader)
  | None ->
    match find_interfaces_dir Sys.executable_name with
    | Some interface_dir ->
      let file_name = String.uncapitalize_ascii (Name.to_string module_name) in
      let file_name = Filename.concat interface_dir (file_name ^ ".interface") in
      if Sys.file_exists file_name then
        let (wmod, loader) = add_interface env "OCaml" loader file_name in
        (Some wmod, loader)
      else
        (None, loader)
    | None ->
      prerr_endline @@ to_string 80 2 (!^ "Warning: interfaces directory was not found");
      (None, loader)
