(* Inferring effects through match statements. *)
exception Ex1
exception Ex2 of int

let f () = raise Ex1
let g (y : int) = raise (Ex2 y)
let h () (y : int) () = raise (Ex2 y)

let x = (f, g, h)

let f' = let (f, _, _) = x in f
let g' = let (_, g, _) = x in g
let h' = let (_, _, h) = x in h

let (f'', g'', h'') = x

let ff = match x with (f, _, _) -> f
let gg = match x with (_, g, _) -> g
let hh = match x with (_, _, h) -> h

let fff : unit -> unit = let (f, _, _) = x in f
let ggg : int -> unit = let (_, g, _) = x in g
let hhh : unit -> int -> unit -> unit = let (_, _, h) = x in h

let f1 = match f with x -> x
let g1 = match g with x -> x
let h1 = match h with x -> x
