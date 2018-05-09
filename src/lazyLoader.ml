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

let find_first (f : 'a -> 'b option) (l : 'a list) : 'b option =
  FullMod.find_first f l

(* Mutable list of Coq name, interface directory pairs. *)
let interfaces : (Name.t * string) list ref = ref []

let find_wrapped_mod_opt (env : Effect.Type.t FullEnvi.t) (loader : 'a t)
  (module_name : Name.t) : 'a FullEnvi.WrappedMod.t option * 'a t =
  match Name.Map.find_opt module_name loader with
  | Some wmod -> (Some wmod, loader)
  | None ->
    let file_name = String.uncapitalize_ascii (Name.to_string module_name) in
    match find_first (fun (coq_prefix, dir) ->
        let file_name = Filename.concat dir (file_name ^ ".interface") in
        if Sys.file_exists file_name then Some (coq_prefix, file_name) else None)
      !interfaces with
    | Some (coq_prefix, file_name) ->
      let (wmod, loader) = add_interface env coq_prefix loader file_name in
      (Some wmod, loader)
    | None -> (None, loader)
