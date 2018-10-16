open SmartPrint
open Yojson.Basic
open Utils

type t =
  | Var of CoqName.t * Type.t
  | Typ of TypeDefinition.t
  | TypeExt of PathName.t * TypeDefinition.t
  | Descriptor of CoqName.t
  | Exception of CoqName.t * CoqName.t
  | Include of PathName.t
  | Interface of CoqName.t * t list
  | Signature of CoqName.t * t list

let rec pp (interface : t) : SmartPrint.t =
  match interface with
  | Var (x, shape) ->
    !^ "Var" ^^ OCaml.tuple [CoqName.pp x; Effect.pp shape]
  | Typ def -> !^ "Typ" ^^ TypeDefinition.pp def
  | TypeExt (name, def) ->
    !^ "TypeExt" ^^ PathName.pp name ^^ TypeDefinition.pp def
  | Descriptor x -> !^ "Descriptor" ^^ CoqName.pp x
  | Exception (x, typ_name) ->
    !^ "Exception" ^^ OCaml.tuple [CoqName.pp x; CoqName.pp typ_name]
  | Include x -> !^ "Include" ^^ PathName.pp x
  | Interface (x, defs) ->
    !^ "Interface" ^^ CoqName.pp x ^^ !^ "=" ^^ newline ^^ indent
      (separate newline (List.map pp defs))
  | Signature (x, defs) ->
    !^ "Signature" ^^ CoqName.pp x ^^ !^ "=" ^^ newline ^^ indent
      (separate newline (List.map pp defs))

let rec of_signatures (decls : Signature.t list) : t list =
  List.flatten (List.map of_signature decls)

and of_signature (decl : Signature.t) : t list =
  match decl with
  | Signature.Value (_, name, typ_vars, typ) -> [Var (name, Effect.pure)]
  | Signature.TypeDefinition (_, typ_def) -> [Typ typ_def]
  | Signature.Module (_, name, decls) ->
    [Interface (name, of_signatures decls)]
  | Signature.ModType (_, name, decls) ->
    [Signature (name, of_signatures decls)]

let rec of_structures (defs : ('a * Type.t) Structure.t list) : t list =
  List.flatten (List.map of_structure defs)

and of_structure (def : ('a * Type.t) Structure.t) : t list =
  match def with
  | Structure.Require names -> []
  | Structure.Value (_, value) ->
    value.Exp.Definition.cases |> List.map (fun (header, e) ->
      let name = header.Exp.Header.name in
      let typ =
        Effect.function_typ header.Exp.Header.args (snd (Exp.annotation e)) in
      Var (name, typ))
  | Structure.Primitive (_, prim) ->
    (* TODO: Update to reflect that primitives are not usually pure. *)
    [Var (prim.PrimitiveDeclaration.name, Effect.pure)]
  | Structure.TypeDefinition (_, typ_def) -> [Typ typ_def]
  | Structure.TypeExt (_, typ_ext) ->
    [TypeExt (typ_ext.TypeExt.typ.BoundName.full_path, typ_ext.TypeExt.typ_def)]
  | Structure.Exception (_, exn) ->
    [Exception (exn.Exception.name, exn.Exception.typ_name)]
  | Structure.Reference (_, r) ->
    [Descriptor r.Reference.state_name;
     Var (r.Reference.name, r.Reference.effect)]
  | Structure.Open _ -> []
  | Structure.Include (_, name) -> [Include name.local_path]
  | Structure.Module (_, name, defs) ->
    [Interface (name, of_structures defs)]
  | Structure.Signature (_, name, decls) ->
    [Signature (name, of_signatures decls)]

let rec to_full_envi (interface : t) (env : Type.t FullEnvi.t)
  : Type.t FullEnvi.t =
  match interface with
  | Var (x, effect) -> FullEnvi.Var.assoc x effect env
  | Typ typ -> TypeDefinition.update_env typ env
  | TypeExt (typ, typ_def) ->
    let typ = FullEnvi.Typ.localize env typ.PathName.path typ.PathName.base in
    TypeExt.update_env { TypeExt.typ; typ_def} env
  | Descriptor x -> FullEnvi.Descriptor.assoc x () env
  | Exception (name, typ_name) ->
    env |> Exception.update_env
      { Exception.name; typ_name; typ = Type.Variable "_" }
  | Include x -> Include.of_interface x env
  | Interface (x, defs) ->
    let env = FullEnvi.enter_module x env in
    let env = List.fold_left (fun env def -> to_full_envi def env) env
      defs in
    FullEnvi.leave_module env
  | Signature (x, decls) ->
    let env = FullEnvi.enter_module x env in
    let env = List.fold_left (fun env def -> to_full_envi def env) env
      decls in
    FullEnvi.leave_signature env

let load_interface (coq_prefix : Name.t) (interface : t)
  (env : Type.t FullEnvi.t) : Name.t * Type.t FullEnvi.t =
  let name = match interface with
    | Interface (name, _) -> CoqName.ocaml_name name
    | _ -> "" in
  let coq_name = if coq_prefix == "" || name == "" then coq_prefix ^ name
    else coq_prefix ^ "." ^ name in
  let env = to_full_envi interface env in
  (coq_name, env)

let rec to_json (interface : t) : json =
  match interface with
  | Var (x, eff) ->
    `List [`String "Var"; CoqName.to_json x; Effect.to_json eff]
  | Typ x -> `List [`String "Typ"; TypeDefinition.to_json x]
  | TypeExt (name, x) ->
    `List [`String "TypeExt"; PathName.to_json name; TypeDefinition.to_json x]
  | Descriptor x -> `List [`String "Descriptor"; CoqName.to_json x]
  | Exception (name, typ_name) ->
    `List [`String "Exception"; CoqName.to_json name; CoqName.to_json typ_name]
  | Include x -> `List [`String "Include"; PathName.to_json x]
  | Interface (x, defs) ->
    `List [`String "Interface"; CoqName.to_json x; `List (List.map to_json defs)]
  | Signature (x, defs) ->
    `List [`String "Signature"; CoqName.to_json x; `List (List.map to_json defs)]

let rec of_json (json : json) : t =
  match json with
  | `List [`String "Var"; x; eff] ->
    Var (CoqName.of_json x, Effect.of_json eff)
  | `List [`String "Typ"; x] -> Typ (TypeDefinition.of_json x)
  | `List [`String "TypeExt"; name; x] ->
    TypeExt (PathName.of_json name, TypeDefinition.of_json x)
  | `List [`String "Descriptor"; x] -> Descriptor (CoqName.of_json x)
  | `List [`String "Exception"; name; typ_name] ->
    Exception (CoqName.of_json name, CoqName.of_json typ_name)
  | `List [`String "Include"; x] -> Include (PathName.of_json x)
  | `List [`String "Interface"; x; `List defs] ->
      Interface (CoqName.of_json x, List.map of_json defs)
  | `List [`String "Signature"; x; `List defs] ->
      Signature (CoqName.of_json x, List.map of_json defs)
  | _ -> raise (Error.Json
    "Expected a Var, Typ, Descriptor, Signature or Interface field.")

let to_json_string (interface : t) : string =
  let pretty = pretty_format ~std:true (`Assoc [
    "version", `String "2";
    "content", to_json interface]) in
  let buffer = Buffer.create 0 in
  let formatter = Format.formatter_of_buffer buffer in
  Format.pp_set_margin formatter 120;
  Easy_format.Pretty.to_formatter formatter pretty;
  Format.pp_print_flush formatter ();
  Buffer.contents buffer

let of_json_string (json : string) : t =
  match from_string json with
  | `Assoc jsons ->
    (match List.assoc "version" jsons with
    | `String "2" -> of_json @@ List.assoc "content" jsons
    | _ -> raise (Error.Json "Wrong interface version, expected 2."))
  | _ -> raise (Error.Json "Expected an object.")

let of_file (file_name : string) : t =
  let file =
    try open_in_bin file_name with
    | Sys_error _ ->
      open_in_bin (Filename.dirname Sys.executable_name ^
        "/../share/coq-of-ocaml/" ^ file_name) in
  let size = in_channel_length file in
  let content = Bytes.make size ' ' in
  really_input file content 0 size;
  of_json_string (Bytes.to_string content)

let load_module (module_name : Name.t) (env : Type.t FullEnvi.t)
  : Type.t FullEnvi.t =
    let file_name = String.uncapitalize_ascii (Name.to_string module_name) in
    match find_first (fun (coq_prefix, dir) ->
        let file_name = Filename.concat dir (file_name ^ ".interface") in
        if Sys.file_exists file_name then Some (coq_prefix, file_name) else None)
      env.interfaces with
    | Some (coq_prefix, file_name) ->
      let interface = of_file file_name in
      let (module_name, env) = load_interface coq_prefix interface env in
      FullEnvi.module_required module_name env;
      env
    | None -> env
