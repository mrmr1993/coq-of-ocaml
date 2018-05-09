module WrappedMod = struct
  type 'a t = {
    m : 'a Mod.t;
    ocaml_name : Name.t;
    coq_name : Name.t
  }

  let map (f : 'a -> 'b) (wmod : 'a t) : 'b t =
    {wmod with m = Mod.map f wmod.m}
end

type 'a t = 'a WrappedMod.t Name.Map.t

let empty = Name.Map.empty

(* NOTE: This is designed under the assumption that
   - |ocaml_name| is a top-level name (ie. contains no '.' characters)
   - no two modules share the same |ocaml_name|
   - |coq_name| is some path name, followed by '.', followed by |ocaml_name| *)
let add_wrapped_mod (wmod : 'a WrappedMod.t) (loader : 'a t) : 'a t =
  loader
  |> Name.Map.add wmod.ocaml_name wmod
  |> Name.Map.add wmod.coq_name wmod

let find_wrapped_mod_opt (module_name : Name.t) (loader : 'a t) : 'a WrappedMod.t option =
  Name.Map.find_opt module_name loader

let find_wrapped_mod (module_name : Name.t) (loader : 'a t) : 'a WrappedMod.t =
  Name.Map.find module_name loader

let map (f : 'a -> 'b) (loader : 'a t) : 'b t =
  Name.Map.map (WrappedMod.map f) loader
