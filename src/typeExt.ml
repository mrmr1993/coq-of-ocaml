open Types
open Typedtree
open SmartPrint
open Utils

type t = {
  typ : BoundName.t;
  typ_def : TypeDefinition.t;
}

let of_ocaml (env : 'a FullEnvi.t) (loc : Loc.t) (typext : type_extension) : t =
  let path = PathName.of_path loc typext.tyext_path in
  let typ = FullEnvi.Typ.bound loc path env in
  let (x, x_bound, env) = FullEnvi.Typ.fresh path.PathName.base
    (Abstract (CoqName.Name path.PathName.base, [])) env in
  let typ_args = typext.tyext_params |> List.map (fun (arg, _) ->
    Type.of_type_expr_variable loc arg.ctyp_type) in
  let constructors = typext.tyext_constructors |> ((0, env) |>
    map_with_acc (fun (index, env) { ext_id = constr; ext_type = exttyp } ->
      let typs =
        match exttyp.ext_args with
        | Cstr_tuple typs -> typs
        | Cstr_record _ -> Error.raise loc "Unhandled named constructor parameters." in
      let constr = Name.of_ident constr in
      let typs = List.map (fun typ -> Type.of_type_expr env loc typ) typs in
      let (constr, _, env) = FullEnvi.Constructor.create constr
        (x_bound.BoundName.full_path, index) env in
      ((1 + index, env), (constr, typs)))) in
  { typ; typ_def = TypeDefinition.Inductive (x, typ_args, constructors) }

let pp (ext : t) : SmartPrint.t =
  OCaml.tuple [BoundName.pp ext.typ; TypeDefinition.pp ext.typ_def]

let update_env (ext : t) (env : 'a FullEnvi.t) : 'a FullEnvi.t =
  TypeDefinition.update_env ext.typ_def env

let to_coq (ext : t) : SmartPrint.t =
  TypeDefinition.to_coq ext.typ_def
