open SmartPrint

type t = {
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

let resolve_open (name : PathName.t) (x : t) : t =
  if x.depth = 1 then
    { path_name = { x.path_name with
        PathName.path = PathName.to_name_list name @ x.path_name.path };
      depth = 0 }
  else if x.depth > 1 then
    { x with depth = x.depth - 1 }
  else
    x

let to_coq (x : t) : SmartPrint.t =
  PathName.to_coq x.path_name
