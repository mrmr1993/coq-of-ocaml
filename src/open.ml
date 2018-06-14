open SmartPrint

type t = PathName.t

let pp (o : t) : SmartPrint.t =
  nest (!^ "Open" ^^ PathName.pp o)

let of_ocaml (loc : Loc.t) (path : Path.t) : t =
  PathName.of_path loc path

let update_env_struct (loc : Loc.t) (o : t) (env : 'a FullEnvi.t)
  : t * 'a FullEnvi.t =
  FullEnvi.open_module_struct loc o env

let update_env (loc : Loc.t) (o : t) (env : 'a FullEnvi.t) : 'a FullEnvi.t =
  FullEnvi.open_module loc o env

let update_env_nocheck (o : t) (env : 'a FullEnvi.t) : 'a FullEnvi.t =
  FullEnvi.open_module_nocheck o env

(** Pretty-print an open construct to Coq. *)
let to_coq (o : t): SmartPrint.t =
  nest (!^ "Import" ^^ PathName.pp o ^-^ !^ ".")
