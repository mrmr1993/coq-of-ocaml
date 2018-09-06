open SmartPrint

type t = {
  full_path : PathName.t;
  local_path : PathName.t;
  path_name : PathName.t;
  depth : int }

let pp (x : t) : SmartPrint.t =
  PathName.pp x.path_name ^-^ !^ "/" ^-^ OCaml.int x.depth

let depth_lift (x : t) : t =
  { x with depth = x.depth + 1 }

let leave_prefix (name : Name.t option) (x : t) : t =
  if x.depth = 0 then
    match name with
    | Some name ->
      { x with path_name = { x.path_name with
        PathName.path = name :: x.path_name.PathName.path } }
    | None -> x
  else if x.depth > 0 then
    { x with depth = x.depth - 1 }
  else
    x

let resolve_open (name_list : Name.t list) (x : t) : t =
  if x.depth = 1 then
    { x with
      path_name = { x.path_name with
        PathName.path = name_list @ x.path_name.path };
      depth = 0 }
  else if x.depth > 1 then
    { x with depth = x.depth - 1 }
  else
    x

(* Compare on the base name first, for better stability across modules. *)
let stable_compare (x : t) (y : t) : int =
  compare x.full_path y.full_path

let to_coq (x : t) : SmartPrint.t =
  PathName.to_coq x.local_path
