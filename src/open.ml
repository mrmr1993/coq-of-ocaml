open SmartPrint

type t = BoundName.t

let pp (o : t) : SmartPrint.t =
  nest (!^ "Open" ^^ BoundName.pp o)

let of_ocaml (env : 'a FullEnvi.t) (loc : Loc.t) (path : Path.t) : t =
  let path = PathName.of_path loc path in
  FullEnvi.Module.bound loc path env

let update_env (loc : Loc.t) (o : t) (env : 'a FullEnvi.t) : 'a FullEnvi.t =
  FullEnvi.open_module loc o env

(** Pretty-print an open construct to Coq. *)
let to_coq (o : t): SmartPrint.t =
  nest (!^ "Import" ^^ BoundName.to_coq o ^-^ !^ ".")
