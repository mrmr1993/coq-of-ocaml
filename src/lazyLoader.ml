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
  (loader : Effect.Type.t t) (file_name : string) : 'a t =
  let interface = Interface.of_file file_name in
  let wmod = Interface.to_wrapped_mod coq_prefix interface env in
  add_wrapped_mod wmod loader

let find_wrapped_mod_opt (loader : 'a t) (module_name : Name.t)
  : 'a FullEnvi.WrappedMod.t option =
  Name.Map.find_opt module_name loader
