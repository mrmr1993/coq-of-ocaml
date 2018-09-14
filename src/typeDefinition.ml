open Types
open Typedtree
open SmartPrint
open Utils

type t =
  | Inductive of CoqName.t * Name.t list * (CoqName.t * Type.t list) list
  | Record of CoqName.t * (CoqName.t * Type.t) list
  | Synonym of CoqName.t * Name.t list * Type.t
  | Abstract of CoqName.t * Name.t list

let pp (def : t) : SmartPrint.t =
  match def with
  | Inductive (name, typ_args, constructors) ->
    nest (!^ "Inductive" ^^ CoqName.pp name ^-^ !^ ":" ^^ newline ^^
      indent (OCaml.tuple [
        OCaml.list Name.pp typ_args;
        constructors |> OCaml.list (fun (x, typs) ->
          OCaml.tuple [CoqName.pp x; OCaml.list Type.pp typs])]))
  | Record (name, fields) ->
    nest (!^ "Record" ^^ CoqName.pp name ^-^ !^ ":" ^^ newline ^^
      indent (fields |> OCaml.list (fun (x, typ) ->
        OCaml.tuple [CoqName.pp x; Type.pp typ])))
  | Synonym (name, typ_args, value) ->
    nest (!^ "Synonym" ^^ OCaml.tuple [
      CoqName.pp name; OCaml.list Name.pp typ_args; Type.pp value])
  | Abstract (name, typ_args) ->
    nest (!^ "Abstract" ^^ OCaml.tuple [
      CoqName.pp name; OCaml.list Name.pp typ_args])

let of_declaration (env : unit FullEnvi.t) (loc : Loc.t)
  (name : Ident.t) (typ : Types.type_declaration) : t =
  let (x, _, env) = FullEnvi.Typ.create (Name.of_ident name) () env in
  let typ_args =
    List.map (Type.of_type_expr_variable loc) typ.type_params in
  (match typ.type_kind with
  | Type_variant cases ->
    let constructors = cases |> (env |>
      map_with_acc (fun env { Types.cd_id = constr; cd_args = args } ->
        let typs =
          match args with
          | Cstr_tuple typs -> typs
          | Cstr_record _ -> Error.raise loc "Unhandled named constructor parameters." in
        let constr = Name.of_ident constr in
        let (constr, _, env) = FullEnvi.Constructor.create constr env in
        (env, (constr, typs |> List.map (fun typ ->
          Type.of_type_expr env loc typ))))) in
    Inductive (x, typ_args, constructors)
  | Type_record (fields, _) ->
    let fields = fields |> (env |>
      map_with_acc (fun env { Types.ld_id = x; ld_type = typ } ->
        let field_name = FullEnvi.Field.coq_name (Name.of_ident x) env in
        (env, (field_name, Type.of_type_expr env loc typ)))) in
    Record (x, fields)
  | Type_abstract ->
    (match typ.type_manifest with
    | Some typ -> Synonym (x, typ_args, Type.of_type_expr env loc typ)
    | None -> Abstract (x, typ_args))
    | Type_open -> Error.raise loc "Open type definition not handled.")

let of_ocaml (env : unit FullEnvi.t) (loc : Loc.t)
  (typs : type_declaration list) : t =
  match typs with
  | [] -> Error.raise loc "Unexpected type definition with no case."
  | [{typ_id = name; typ_type = typ}] -> of_declaration env loc name typ
  | typ :: _ :: _ -> Error.raise loc "Type definition with 'and' not handled."

let update_env (def : t) (v : 'a) (env : 'a FullEnvi.t) : 'a FullEnvi.t =
  match def with
  | Inductive (name, _, constructors) ->
    let env = FullEnvi.Typ.assoc name v env in
    List.fold_left (fun env (x, _) ->
      FullEnvi.Constructor.assoc x env)
      env constructors
  | Record (name, fields) ->
    let env = FullEnvi.Typ.assoc name v env in
    List.fold_left (fun env (x, _) -> FullEnvi.Field.assoc x env)
      env fields
  | Synonym (name, _, _) | Abstract (name, _) ->
    FullEnvi.Typ.assoc name v env

let to_coq (def : t) : SmartPrint.t =
  match def with
  | Inductive (name, typ_args, constructors) ->
    nest (
      !^ "Inductive" ^^ CoqName.to_coq name ^^
      (if typ_args = []
      then empty
      else parens @@ nest (
        separate space (List.map Name.to_coq typ_args) ^^
        !^ ":" ^^ !^ "Type")) ^^
      !^ ":" ^^ !^ "Type" ^^ !^ ":=" ^-^
      separate empty (constructors |> List.map (fun (constr, args) ->
        newline ^^ nest (
          !^ "|" ^^ CoqName.to_coq constr ^^ !^ ":" ^^
          separate space (args |> List.map (fun arg -> Type.to_coq true arg ^^ !^ "->")) ^^
          separate space (CoqName.to_coq name :: List.map Name.to_coq typ_args)))) ^-^ !^ "." ^^
      separate empty (constructors |> List.map (fun (name, args) ->
        if typ_args = [] then
          empty
        else
          newline ^^ nest (separate space (
            !^ "Arguments" :: CoqName.to_coq name ::
            (List.map (fun x -> braces @@ Name.to_coq x) typ_args) @
            (List.map (fun _ -> !^ "_") args)) ^-^ !^ "."))))
  | Record (name, fields) ->
    nest (
      !^ "Record" ^^ CoqName.to_coq name ^^ !^ ":=" ^^ !^ "{" ^^ newline ^^
      indent (separate (!^ ";" ^^ newline) (fields |> List.map (fun (x, typ) ->
        nest (CoqName.to_coq x ^^ !^ ":" ^^ Type.to_coq false typ)))) ^^
      !^ "}.")
  | Synonym (name, typ_args, value) ->
    nest (
      !^ "Definition" ^^ CoqName.to_coq name ^^
      separate space (List.map Name.to_coq typ_args) ^^ !^ ":=" ^^
      Type.to_coq false value ^-^ !^ ".")
  | Abstract (name, typ_args) ->
    nest (
      !^ "Parameter" ^^ CoqName.to_coq name ^^ !^ ":" ^^
      (match typ_args with
      | [] -> empty
      | _ :: _ ->
        !^ "forall" ^^ braces (group (
          separate space (List.map Name.to_coq typ_args) ^^
          !^ ":" ^^ !^ "Type")) ^-^ !^ ",") ^^
      !^ "Type" ^-^ !^ ".")
