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

let find_wrapped_mod_opt (loader : 'a t) (module_name : Name.t)
  : 'a FullEnvi.WrappedMod.t option =
  Name.Map.find_opt module_name loader
