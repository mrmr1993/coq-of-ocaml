open SmartPrint
open Utils

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
  | None -> Interface.load_module !interfaces module_name env
