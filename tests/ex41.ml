module type S = sig
  val x : int
  val y : bool
  val z : ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'c

  type t =
  | Inductive1
  | Inductive2 of int
  | Inductive3 of bool

  type 'a u = ('a * t) list
  
  module X : sig
    val x : bool
    val y : int
  end

  module type S = sig
    val x : bool
    val y : int
  end
end
