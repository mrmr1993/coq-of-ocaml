(** Open type definitions *)
type t = ..

let f () : t = assert false

type 'a u = ..

let g (x : 'a) : 'a u = failwith "fail"

type t += Test1 | Test2 of bool

type t += Test3 of int | Test4 of int option

type 'b u += Test5 of 'b | Test6 of int

let x = Test1

let y = Test5 5

let z = Test6 6

let failure = Failure ""
