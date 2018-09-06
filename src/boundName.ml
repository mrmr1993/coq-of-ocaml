open SmartPrint

type t = {
  full_path : PathName.t;
  local_path : PathName.t;
  depth : int }

let pp (x : t) : SmartPrint.t =
  PathName.pp x.local_path ^-^ !^ "/" ^-^ OCaml.int x.depth

let depth_lift (x : t) : t =
  { x with depth = x.depth + 1 }

let leave_prefix (x : t) : t =
  if x.depth > 0 then
    { x with depth = x.depth - 1 }
  else
    x

let resolve_open (x : t) : t =
  if x.depth = 1 then
    { x with depth = 0 }
  else if x.depth > 1 then
    { x with depth = x.depth - 1 }
  else
    x

(* Compare on the base name first, for better stability across modules. *)
let stable_compare (x : t) (y : t) : int =
  compare x.full_path y.full_path

let to_coq (x : t) : SmartPrint.t =
  PathName.to_coq x.local_path
