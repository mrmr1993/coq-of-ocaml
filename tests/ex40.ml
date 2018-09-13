(** Test unique names for toplevel definitions. *)

let a = ref 15
let b () = a
let a = ref "test"
let c () = a

let d = 15
let e = d
let d = "test"
let f = d

external ( = ) : 'a -> 'a -> bool = "%equal"
let g x y = x = y
external ( = ) : 'a -> 'a -> bool = "%equal"
let h x y = x = y
