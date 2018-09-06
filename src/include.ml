open SmartPrint

type t = BoundName.t

let pp (incl : t) : SmartPrint.t =
  nest (!^ "Include" ^^ (BoundName.pp incl))

let of_ocaml (env : 'a FullEnvi.t) (loc : Loc.t) (path : Path.t) : t =
  let path = PathName.of_path loc path in
  FullEnvi.Module.bound loc path env

let update_env (loc : Loc.t) (incl : t) (env : 'a FullEnvi.t)
  : 'a FullEnvi.t =
  let mod_body = FullEnvi.Module.find loc incl env (fun x -> x) in
  FullEnvi.include_module mod_body env

let of_interface (path : PathName.t) (env : 'a FullEnvi.t) =
  let bound_module = FullEnvi.Module.bound Loc.Unknown path env in
  update_env Loc.Unknown bound_module env

(** Pretty-print an include construct to Coq. *)
let to_coq (incl : t): SmartPrint.t =
  nest (!^ "Include" ^^ BoundName.to_coq incl ^-^ !^ ".")
