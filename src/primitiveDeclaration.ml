open Types
open Typedtree
open SmartPrint

type t = {
  name : Name.t;
  typ : Type.t }

let pp (prim : t) : SmartPrint.t =
  nest (!^ "Primitive" ^^ OCaml.tuple [Name.pp prim.name; Type.pp prim.typ])

let to_coq (prim : t) : SmartPrint.t =
  concat [!^ "Parameter" ^^ Name.to_coq prim.name ^^ !^ ":" ^^
  Type.to_coq true prim.typ; !^ "."]

let of_ocaml (env : unit FullEnvi.t) (loc : Loc.t) (desc : value_description)
  : t =
    { name = Name.of_ident desc.val_id;
      typ = Type.of_type_expr env loc desc.val_val.val_type }

let update_env (prim : t) (env : unit FullEnvi.t) : unit FullEnvi.t =
  FullEnvi.add_var [] prim.name () env

(* TODO: Update to reflect that primitives are not usually pure. *)
let update_env_with_effects (prim : t) (env : Effect.Type.t FullEnvi.t)
  : Effect.Type.t FullEnvi.t =
  FullEnvi.add_var [] prim.name Effect.Type.Pure env
