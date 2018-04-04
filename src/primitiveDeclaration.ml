open Types
open Typedtree
open SmartPrint

type t = {
  name : Name.t;
  typ_args : Name.t list;
  typ : Type.t }

let pp (prim : t) : SmartPrint.t =
  nest (!^ "Primitive" ^^
    OCaml.tuple
      [Name.pp prim.name; OCaml.list Name.pp prim.typ_args; Type.pp prim.typ])


let get_type_params (typ : type_expr) : Name.t list =
  let params = ref Name.Set.empty in
  let rec get_params typ =
    match typ.desc with
    | Tvar (Some name) -> params := Name.Set.add (Name.of_string name) !params
    | _ -> Btype.iter_type_expr get_params typ
  in get_params typ;
  Name.Set.elements !params

let to_coq (prim : t) : SmartPrint.t =
  nest (
    !^ "Parameter" ^^ Name.to_coq prim.name ^^ !^ ":" ^^
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
    { name = Name.of_ident desc.val_id;
      typ_args = get_type_params type_expr;
      typ = Type.of_type_expr env loc type_expr }

let update_env (prim : t) (env : unit FullEnvi.t) : unit FullEnvi.t =
  FullEnvi.add_var [] prim.name () env

(* TODO: Update to reflect that primitives are not usually pure. *)
let update_env_with_effects (prim : t) (env : Effect.Type.t FullEnvi.t)
  : Effect.Type.t FullEnvi.t =
  FullEnvi.add_var [] prim.name Effect.Type.Pure env
