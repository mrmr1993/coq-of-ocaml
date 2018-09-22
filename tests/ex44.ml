(** Toplevel destructuring assignments. *)

let () = ignore (1 + 1)

let (a, b) = (15, "hi")

type a = A of int * bool

let A (i, j) = A (15, true)

type b = { first : int; second : bool; third : string }

let b_val = { first = 12; second = false; third = "hello" }

let { first = hi } = b_val
let { second = hey } = b_val
let { second = hey; third = hello } = b_val

let { first = first; second = second; third = third } =
  { first = hi; second = hey; third = hello }
