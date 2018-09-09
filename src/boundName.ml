open SmartPrint
open Utils

type t = {
  full_path : PathName.t;
  local_path : PathName.t;
  }

let pp (x : t) : SmartPrint.t =
  let full_path_prefix = drop (List.length x.local_path.PathName.path)
    x.full_path.PathName.path in
  let local = PathName.pp x.local_path in
  match full_path_prefix with
  | [] -> local
  | _ ->
    separate (!^ ".") (List.map Name.pp full_path_prefix) ^-^ !^ "/" ^-^
      local

(* Compare on the base name first, for better stability across modules. *)
let stable_compare (x : t) (y : t) : int =
  compare x.full_path y.full_path

let to_coq (x : t) : SmartPrint.t =
  PathName.to_coq x.local_path
