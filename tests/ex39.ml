(* References as local values *)

let get_local_ref (tt : unit) : int =
  let x = ref 12 in
  !x

let set_local_ref (tt : unit) : int =
  let x = ref 12 in
  x := 15;
  !x

let add_multiple_by_refs a b c d : int =
  let x = ref a in
  x := !x + b;
  let y = ref c in
  y := !y + d;
  let z = ref (!x + !y) in
  !z

