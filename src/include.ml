open Typedtree
open SmartPrint

type t = PathName.t

let pp (incl : t) : SmartPrint.t =
  nest (!^ "Include" ^^ (PathName.pp incl))

let of_ocaml (loc : Loc.t) (path : Path.t) : t =
  PathName.of_path loc path

let update_env (loc : Loc.t) (incl : t) (env : 'a FullEnvi.t)
  : 'a FullEnvi.t =
  let bound_mod = FullEnvi.bound_module loc incl env in
  let mod_body = FullEnvi.find_module bound_mod env (fun x -> x) in
  FullEnvi.include_module loc mod_body env

let of_interface (path : PathName.t) (env : 'a FullEnvi.t) =
  update_env Loc.Unknown path env

(** Pretty-print an open construct to Coq. *)
let to_coq (incl : t): SmartPrint.t =
  nest (!^ "Include" ^^ PathName.pp incl ^-^ !^ ".")
