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

let set_ref (x : int ref) : unit =
  x := 15

let get_ref (x : int ref) : int =
  !x

let update_ref (x : int ref) : unit =
  x := !x + 5

let new_ref (x : unit) : int ref =
  ref 15

let r : int ref = ref 18

let set_r (x : unit) : unit = set_ref r

let get_r (x : unit) : int = get_ref r

let r_add_15 (x : unit) : int =
  let i = get_r () in
  set_r ();
  let j = get_r () in
  r := i + j;
  !r

let mixed_type (x : unit) : bool * string * int =
  let b = ref true in
  let str = ref "" in
  let update () =
    b := !b;
    str := "toggle " ^ !str in
  update ();
  update ();
  update ();
  (!b, !str, !r)
