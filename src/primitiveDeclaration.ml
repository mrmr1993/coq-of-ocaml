open SmartPrint

type t = unit

let pp (value : t) : SmartPrint.t = nest (!^ "Primitive")

let to_coq (value : t) : SmartPrint.t = !^ ""
