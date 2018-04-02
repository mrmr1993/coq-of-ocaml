open SmartPrint

type t = unit

let pp (value : t) : SmartPrint.t = nest (!^ "Primitive")

let to_coq (value : t) : SmartPrint.t = !^ ""

let of_ocaml env loc val_desc = ()

let update_env prim env = env
