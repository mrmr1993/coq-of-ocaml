open Types
open Typedtree
open SmartPrint
open Yojson.Basic
open Utils

include Kerneltypes.TypeDefinition

let pp (def : t) : SmartPrint.t =
  match def with
  | Inductive (name, typ_args, constructors) ->
    nest (!^ "Inductive" ^^ CoqName.pp name ^-^ !^ ":" ^^ newline ^^
      indent (OCaml.tuple [
        OCaml.list Name.pp typ_args;
        constructors |> OCaml.list (fun (x, typs) ->
          OCaml.tuple [CoqName.pp x; OCaml.list Type.pp typs])]))
  | Record (name, typ_args, fields) ->
    nest (!^ "Record" ^^ CoqName.pp name ^-^ !^ ":" ^^ newline ^^
      indent (OCaml.tuple [
        OCaml.list Name.pp typ_args;
        fields |> OCaml.list (fun (x, typ) ->
          OCaml.tuple [CoqName.pp x; Type.pp typ])]))
  | Synonym (name, typ_args, value) ->
    nest (!^ "Synonym" ^^ OCaml.tuple [
      CoqName.pp name; OCaml.list Name.pp typ_args; Type.pp value])
  | Abstract (name, typ_args) ->
    nest (!^ "Abstract" ^^ OCaml.tuple [
      CoqName.pp name; OCaml.list Name.pp typ_args])

let of_declaration (env : unit FullEnvi.t) (loc : Loc.t)
  (name : Ident.t) (typ : Types.type_declaration) : t =
  let name = Name.of_ident name in
  let (x, x_bound, env) = FullEnvi.Typ.create name
    (Abstract (CoqName.Name name, [])) env in
  let typ_args =
    List.map (Type.of_type_expr_variable loc) typ.type_params in
  match typ.type_kind with
  | Type_variant cases ->
    let constructors = cases |> ((0, env) |>
      map_with_acc (fun (index, env) { Types.cd_id = constr; cd_args = args } ->
        let typs =
          match args with
          | Cstr_tuple typs -> typs
          | Cstr_record _ -> Error.raise loc "Unhandled named constructor parameters." in
        let constr = Name.of_ident constr in
        let typs = List.map (fun typ -> Type.of_type_expr env loc typ) typs in
        let (constr, _, env) = FullEnvi.Constructor.create constr
          (x_bound.BoundName.full_path, index) env in
        ((1 + index, env), (constr, typs)))) in
    Inductive (x, typ_args, constructors)
  | Type_record (fields, _) ->
    let fields = fields |> (env |>
      map_with_acc (fun env { Types.ld_id = x; ld_type = typ } ->
        let field_name = FullEnvi.Field.coq_name (Name.of_ident x) env in
        (env, (field_name, Type.of_type_expr env loc typ)))) in
    Record (x, typ_args, fields)
  | Type_abstract ->
    (match typ.type_manifest with
    | Some typ -> Synonym (x, typ_args, Type.of_type_expr env loc typ)
    | None -> Abstract (x, typ_args))
  | Type_open -> Error.raise loc "Open type definition not handled."

let of_ocaml (env : unit FullEnvi.t) (loc : Loc.t)
  (typs : type_declaration list) : t =
  match typs with
  | [] -> Error.raise loc "Unexpected type definition with no case."
  | [{typ_id = name; typ_type = typ}] -> of_declaration env loc name typ
  | typ :: _ :: _ -> Error.raise loc "Type definition with 'and' not handled."

let update_env (def : t) (env : 'a FullEnvi.t) : 'a FullEnvi.t =
  match def with
  | Inductive (name, typ_args, constructors) ->
    let env = FullEnvi.Typ.assoc name def env in
    let path = { PathName.path = []; base = CoqName.ocaml_name name } in
    let bound = FullEnvi.Typ.bound Loc.Unknown path env in
    snd @@ List.fold_left (fun (index, env) (x, typs) ->
      (index + 1,
      FullEnvi.Constructor.assoc x (bound.BoundName.full_path, index) env))
      (0, env) constructors
  | Record (name, typ_args, fields) ->
    let env = FullEnvi.Typ.assoc name def env in
    let path = { PathName.path = []; base = CoqName.ocaml_name name } in
    let bound = FullEnvi.Typ.bound Loc.Unknown path env in
    snd @@ List.fold_left (fun (index, env) (x, typ) ->
      (index + 1,
      FullEnvi.Field.assoc x (bound.BoundName.full_path, index) env))
      (0, env) fields
  | Synonym (name, _, _) | Abstract (name, _) ->
    FullEnvi.Typ.assoc name def env

let field_type (loc : Loc.t) (env : 'a FullEnvi.t) (field : BoundName.t)
  : Type.t * Type.t =
  let (typ, index) = FullEnvi.Field.find loc field env in
  let bound_typ = { BoundName.full_path = typ; local_path = typ } in
  match FullEnvi.Typ.find loc bound_typ env with
  | Record (name, typ_args, fields) ->
    (Type.Apply (bound_typ, List.map (fun x -> Type.Variable x) typ_args),
    snd (List.nth fields index))
  | _ ->
    Error.raise loc @@ SmartPrint.to_string 80 2 @@
    !^ "The type containing field" ^^ BoundName.pp field ^^ !^ "is not a record type."

let constructor_type (loc : Loc.t) (env : 'a FullEnvi.t) (ctor : BoundName.t)
  : Type.t * Type.t list =
  let (typ, index) = FullEnvi.Constructor.find loc ctor env in
  let bound_typ = { BoundName.full_path = typ; local_path = typ } in
  match FullEnvi.Typ.find loc bound_typ env with
  | Inductive (name, typ_args, constructors) ->
    (Type.Apply (bound_typ, List.map (fun x -> Type.Variable x) typ_args),
    snd (List.nth constructors index))
  | _ ->
    Error.raise loc @@ SmartPrint.to_string 80 2 @@
    !^ "The type containing field" ^^ BoundName.pp ctor ^^ !^ "is not an inductive type."

let to_json (def : t) : json =
  match def with
  | Inductive (name, typ_args, constructors) ->
    `List [`String "Inductive"; CoqName.to_json name;
      `List (List.map Name.to_json typ_args);
      `List (constructors |> List.map (fun (ctor, typs) ->
        `List [CoqName.to_json ctor; `List (List.map (Type.to_json) typs)]))]
  | Record (name, typ_args, fields) ->
    `List [`String "Record"; CoqName.to_json name;
      `List (List.map Name.to_json typ_args);
      `List (fields |> List.map (fun (field, typ) ->
        `List [CoqName.to_json field; Type.to_json typ]))]
  | Synonym (name, typ_args, typ) ->
    `List [`String "Synonym"; CoqName.to_json name;
      `List (List.map Name.to_json typ_args);
      Type.to_json typ]
  | Abstract (name, typ_args) ->
    `List [`String "Abstract"; CoqName.to_json name;
      `List (List.map Name.to_json typ_args)]

let of_json (json : json) : t =
  match json with
  | `List [`String "Inductive"; name; `List typ_args; `List constructors] ->
    Inductive (CoqName.of_json name, List.map Name.of_json typ_args,
      constructors |> List.map (fun ctor ->
        match ctor with
        | `List [name; `List typs] ->
          (CoqName.of_json name, List.map Type.of_json typs)
        | _ -> raise (Error.Json "Invalid JSON for Constructor.")))
  | `List [`String "Record"; name; `List typ_args; `List fields] ->
    Record (CoqName.of_json name, List.map Name.of_json typ_args,
      fields |> List.map (fun field ->
        match field with
        | `List [name; typ] -> (CoqName.of_json name, Type.of_json typ)
        | _ -> raise (Error.Json "Invalid JSON for Record.")))
  | `List [`String "Synonym"; name; `List typ_args; typ] ->
    Synonym (CoqName.of_json name, List.map Name.of_json typ_args,
      Type.of_json typ)
  | `List [`String "Abstract"; name; `List typ_args] ->
    Abstract (CoqName.of_json name, List.map Name.of_json typ_args)
  | _ -> raise (Error.Json "Invalid JSON for TypeDefinition.")

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
  | Record (name, typ_args, fields) ->
    nest (
      !^ "Record" ^^ CoqName.to_coq name ^^
      (if typ_args = []
      then empty
      else parens @@ nest (
        separate space (List.map Name.to_coq typ_args) ^^
        !^ ":" ^^ !^ "Type")) ^^
        !^ ":" ^^ !^ "Type" ^^ !^ ":=" ^^ !^ "{" ^^ newline ^^
      indent (separate (!^ ";" ^^ newline) (fields |> List.map (fun (x, typ) ->
        nest (CoqName.to_coq x ^^ !^ ":" ^^ Type.to_coq false typ)))) ^^
      !^ "}." ^^
      separate empty (fields |> List.map (fun (name, args) ->
        if typ_args = [] then
          empty
        else
          newline ^^ nest (separate space (
            !^ "Arguments" :: CoqName.to_coq name ::
            (List.map (fun x -> braces @@ Name.to_coq x) typ_args) @
            [!^ "_"]) ^-^ !^ "."))))
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
