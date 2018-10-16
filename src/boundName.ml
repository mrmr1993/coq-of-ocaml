open SmartPrint
open Yojson.Basic
open Utils

type t = {
  full_path : PathName.t;
  local_path : PathName.t;
  }

let pp (x : t) : SmartPrint.t =
  let full_path_part = x.full_path.PathName.path in
  let local_path_part = x.local_path.PathName.path in
  let full_path_prefix = take
    (List.length full_path_part - List.length local_path_part) full_path_part in
  let local = PathName.pp x.local_path in
  match full_path_prefix with
  | [] -> local
  | _ ->
    separate (!^ ".") (List.map Name.pp full_path_prefix) ^-^ !^ "/" ^-^
      local

(* Compare on the base name first, for better stability across modules. *)
let stable_compare (x : t) (y : t) : int =
  compare x.full_path y.full_path

let of_name (path : Name.t list) (base : Name.t) =
  let full_path = PathName.of_name path base in
  { full_path; local_path = full_path }

type t' = t
module Set = Set.Make(struct
  type t = t'
  let compare = stable_compare
end)

let to_coq (x : t) : SmartPrint.t =
  PathName.to_coq x.local_path

let to_json (x : t) : json =
  PathName.to_json x.full_path

let of_json (json : json) : t =
  let x = PathName.of_json json in
  { full_path = x; local_path = x }
