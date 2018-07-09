open Types
open Typedtree
open SmartPrint

type t = {
  name : CoqName.t;
  typ_args : Name.t list;
  typ : Type.t }

let pp (prim : t) : SmartPrint.t =
  nest (!^ "Primitive" ^^
    OCaml.tuple [CoqName.pp prim.name; OCaml.list Name.pp prim.typ_args;
      Type.pp prim.typ])

let to_coq (prim : t) : SmartPrint.t =
  nest (
    !^ "Parameter" ^^ CoqName.to_coq prim.name ^^ !^ ":" ^^
    (match prim.typ_args with
    | [] -> empty
    | _ :: _ ->
      !^ "forall" ^^ braces (group (
        separate space (List.map Name.to_coq prim.typ_args) ^^
        !^ ":" ^^ !^ "Type")) ^-^ !^ ",") ^^
    Type.to_coq false prim.typ ^-^ !^ ".")

let of_ocaml (env : unit FullEnvi.t) (loc : Loc.t) (desc : value_description)
  : t =
    let type_expr = desc.val_val.val_type in
    let (typ, _, new_typ_vars) =
      Type.of_type_expr_new_typ_vars env loc Name.Map.empty type_expr in
    let name = Name.of_ident desc.val_id in
    let coq_name = (FullEnvi.resolve_var [] name env).base in
    { name = CoqName.of_names name coq_name;
      typ_args = Name.Set.elements new_typ_vars;
      typ }

let update_env (prim : t) (env : unit FullEnvi.t) : unit FullEnvi.t =
  let (name, coq_name) = CoqName.assoc_names prim.name in
  FullEnvi.assoc_var [] name coq_name () env

(* TODO: Update to reflect that primitives are not usually pure. *)
let update_env_with_effects (prim : t) (env : Effect.Type.t FullEnvi.t)
  : Effect.Type.t FullEnvi.t =
  let (name, coq_name) = CoqName.assoc_names prim.name in
  FullEnvi.assoc_var [] name coq_name Effect.Type.Pure env
