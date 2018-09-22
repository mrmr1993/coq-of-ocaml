(** Toplevel destructuring assignments. *)

let () = ignore (1 + 1)

let (a, b) = (15, "hi")

type a = A of int * bool

let A (i, j) = A (15, true)
