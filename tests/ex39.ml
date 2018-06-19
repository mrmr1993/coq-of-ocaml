(* References as local values *)

let get_local_ref (tt : unit) : int =
  let x = ref 12 in
  !x

let set_local_ref (tt : unit) : int =
  let x = ref 12 in
  x := 15;
  !x

