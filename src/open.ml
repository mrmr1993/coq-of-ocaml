open Typedtree
open SmartPrint

type t = PathName.t

let pp (o : t) : SmartPrint.t =
  nest (!^ "Open" ^^ PathName.pp o)

let of_ocaml (loc : Loc.t) (path : Path.t) : t =
  PathName.of_path loc path

let update_env (o : t) (env : 'a FullEnvi.t) : 'a FullEnvi.t =
  FullEnvi.open_module o env

(** Pretty-print an open construct to Coq. *)
let to_coq (o : t): SmartPrint.t =
  nest (!^ "Import" ^^ PathName.pp o ^-^ !^ ".")
