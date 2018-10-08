open Typedtree
open SmartPrint

type t = {
  name : CoqName.t;
  typ_name : CoqName.t;
  typ : Type.t }

let pp (exn : t) : SmartPrint.t =
  nest (!^ "Exception" ^^
    OCaml.tuple [CoqName.pp exn.name; CoqName.pp exn.typ_name; Type.pp exn.typ])

let of_ocaml (env : unit FullEnvi.t) (loc : Loc.t)
  (exn : extension_constructor) : t =
  let name = Name.of_ident exn.ext_id in
  let typ_name = String.lowercase_ascii name in
  let typs =
    match exn.ext_type.Types.ext_args with
    | Types.Cstr_tuple typs -> typs
    | Types.Cstr_record _ -> Error.raise loc "Unhandled named constructor parameters." in
  let typ = Type.Tuple (typs |> List.map (fun typ -> Type.of_type_expr env loc typ)) in
  let (typ_name, _, env) = FullEnvi.Descriptor.fresh typ_name () env in
  let (name, _, env) = FullEnvi.Var.create name () env in
  { name; typ_name; typ }

let typ_def (exn : t) : TypeDefinition.t =
  TypeDefinition.Inductive (exn.typ_name, [], [(exn.name, [exn.typ])])

let update_env (exn : t) (env : 'a FullEnvi.t) : 'a FullEnvi.t =
  TypeDefinition.update_env (typ_def exn) env

let to_coq (exn : t) : SmartPrint.t =
  TypeDefinition.to_coq (typ_def exn)
