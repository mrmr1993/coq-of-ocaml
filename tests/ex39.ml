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

let partials_test () =
  let f1 (x : int ref) (y : int) : int ref =
    x := y;
    x in
  let f1_test = f1 r in
  let f1_test = f1_test 15 in
  let f2 (l1 : 'a list ref) (l2 : 'b list) : int ref =
    ref (List.length !l1 + List.length l2) in
  let f2_test = f2 (ref [1; 2; 3]) in
  let f2_test = f2_test ["hi"; "hey"] in
  f1 f2_test !f1_test

let multiple_returns_test () =
  let f (x : int ref) (y : int) =
    x := y;
    fun (z : int) -> begin
      x := !x + z;
      fun (w : int ref) -> begin
        let tmp = !w in
        w := 2 * !x;
        x := tmp;
        x
      end
    end in
  let s = ref 110 in
  let f1 = f (ref 5) in
  let f2 = f1 2 in
  let f3 = f2 7 in
  let f4 = f3 s in
  (!f4, s)
