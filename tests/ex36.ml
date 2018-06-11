(** external definitions *)

external ( == ) : bool -> bool -> bool = "%eq"

let all_eqb x y z = x == y && y == z

(* external with polymorphic parameters *)
external ( = ) : 'a -> 'a -> bool = "%eq"

let all_equal x y z = x = y && y = z
