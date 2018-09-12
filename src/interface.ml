open SmartPrint
open Yojson.Basic
open Utils

module Shape = struct
  type t = PathName.t list list

  let rec pp (shape : t) : SmartPrint.t =
    OCaml.list (OCaml.list PathName.pp) shape

  let rec of_effect_typ (typ : Effect.Type.t) : t =
    match typ with
    | Effect.Type.Pure -> []
    | Effect.Type.Arrow (d, typ) ->
      let ds = Effect.Descriptor.elements d |> List.map (fun x ->
        x.BoundName.full_path) in
      ds :: of_effect_typ typ

  let to_effect_typ (shape : t) (env : 'a FullEnvi.t) : Effect.Type.t =
    let descriptor ds : Effect.Descriptor.t =
      let ds = ds |> List.map (fun d ->
        let bound_descriptor = FullEnvi.Descriptor.bound Loc.Unknown d env in
        Effect.Descriptor.singleton bound_descriptor []) in
      Effect.Descriptor.union ds in
    List.fold_right (fun ds typ -> Effect.Type.Arrow (descriptor ds, typ))
      shape Effect.Type.Pure

  let to_json (shape : t) : json =
    `List (List.map (fun ds -> `List (List.map PathName.to_json ds)) shape)

  let of_json (json : json) : t =
    let of_list f json =
      match json with
      | `List jsons -> List.map f jsons
      | _ -> raise (Error.Json "List expected.") in
    of_list (of_list PathName.of_json) json
end

type t =
  | Var of CoqName.t * Shape.t
  | Typ of CoqName.t
  | Descriptor of CoqName.t
  | Constructor of CoqName.t
  | Field of CoqName.t
  | Include of PathName.t
  | Interface of CoqName.t * t list

let rec pp (interface : t) : SmartPrint.t =
  match interface with
  | Var (x, shape) -> !^ "Var" ^^ OCaml.tuple [CoqName.pp x; Shape.pp shape]
  | Typ x -> !^ "Typ" ^^ CoqName.pp x
  | Descriptor x -> !^ "Descriptor" ^^ CoqName.pp x
  | Constructor x -> !^ "Constructor" ^^ CoqName.pp x
  | Field x -> !^ "Field" ^^ CoqName.pp x
  | Include x -> !^ "Include" ^^ PathName.pp x
  | Interface (x, defs) ->
    !^ "Interface" ^^ CoqName.pp x ^^ !^ "=" ^^ newline ^^ indent
      (separate newline (List.map pp defs))

let of_typ_definition (typ_def : TypeDefinition.t) : t list =
  match typ_def with
  | TypeDefinition.Inductive (name, _, constructors) ->
    Typ name :: List.map (fun (x, _) -> Constructor x) constructors
  | TypeDefinition.Record (name, fields) ->
    Typ name :: List.map (fun (x, _) -> Field x) fields
  | TypeDefinition.Synonym (name, _, _) | TypeDefinition.Abstract (name, _) ->
    [Typ name]

let rec of_structures (defs : ('a * Effect.t) Structure.t list) : t list =
  List.flatten (List.map of_structure defs)

and of_structure (def : ('a * Effect.t) Structure.t) : t list =
  match def with
  | Structure.Require names -> []
  | Structure.Value (_, value) ->
    value.Exp.Definition.cases |> List.map (fun (header, e) ->
      let name = header.Exp.Header.name in
      let typ =
        Effect.function_typ header.Exp.Header.args (snd (Exp.annotation e)) in
      Var (name, Shape.of_effect_typ @@ Effect.Type.compress typ))
  | Structure.Primitive (_, prim) ->
    (* TODO: Update to reflect that primitives are not usually pure. *)
    [Var (prim.PrimitiveDeclaration.name, [])]
  | Structure.TypeDefinition (_, typ_def) -> of_typ_definition typ_def
  | Structure.Exception (_, exn) ->
    let name = exn.Exception.name in
    let coq_name = snd @@ CoqName.assoc_names name in
    let raise_name = exn.Exception.raise_name in
    [ Descriptor name; Var (raise_name, [[exn.Exception.effect_path]]) ]
  | Structure.Reference (_, r) ->
    let name = r.Reference.name in
    let state_name = r.Reference.state_name in
    [ Var (name, []); Descriptor state_name ]
  | Structure.Open _ -> []
  | Structure.Include (_, name) -> [Include name.local_path]
  | Structure.Module (_, name, defs) ->
    [Interface (CoqName.of_names name name, of_structures defs)]

let rec to_full_envi (interface : t) (env : Effect.Type.t FullEnvi.t)
  : Effect.Type.t FullEnvi.t =
  match interface with
  | Var (x, shape) -> FullEnvi.Var.assoc x (Shape.to_effect_typ shape env) env
  | Typ x -> FullEnvi.Typ.assoc x Effect.Type.Pure env
  | Descriptor x -> FullEnvi.Descriptor.assoc x env
  | Constructor x -> FullEnvi.Constructor.assoc x env
  | Field x -> FullEnvi.Field.assoc x env
  | Include x -> Include.of_interface x env
  | Interface (x, defs) ->
    let env = FullEnvi.enter_module x env in
    let env = List.fold_left (fun env def -> to_full_envi def env) env defs in
    FullEnvi.leave_module FullEnvi.localize_type env

let load_interface (coq_prefix : Name.t) (interface : t)
  (env : Effect.Type.t FullEnvi.t) : Name.t * Effect.Type.t FullEnvi.t =
  let name = match interface with
    | Interface (name, _) -> CoqName.ocaml_name name
    | _ -> "" in
  let coq_name = if coq_prefix == "" || name == "" then coq_prefix ^ name
    else coq_prefix ^ "." ^ name in
  let env = FullEnvi.enter_module (CoqName.of_names name coq_name) env in
  let env = match interface with
    | Interface (_, defs) ->
      List.fold_left (fun env def -> to_full_envi def env) env defs
    | _ -> to_full_envi interface env in
  (coq_name, FullEnvi.leave_module FullEnvi.localize_type env)

module Version1 = struct
  let rec to_json (interface : t) : json =
    match interface with
    | Var (x, shape) ->
      let x = CoqName.ocaml_name x in
      `List [`String "Var"; Name.to_json x; Shape.to_json shape]
    | Typ x ->
      let x = CoqName.ocaml_name x in
      `List [`String "Typ"; Name.to_json x]
    | Descriptor x ->
      let x = CoqName.ocaml_name x in
      `List [`String "Descriptor"; Name.to_json x]
    | Constructor x ->
      let x = CoqName.ocaml_name x in
      `List [`String "Constructor"; Name.to_json x]
    | Field x ->
      let x = CoqName.ocaml_name x in
      `List [`String "Field"; Name.to_json x]
    | Include x -> `List [`String "Include"; PathName.to_json x]
    | Interface (x, defs) ->
      let x = CoqName.ocaml_name x in
      `List [`String "Interface"; Name.to_json x; `List (List.map to_json defs)]

  let rec of_json (json : json) : t =
    match json with
    | `List [`String "Var"; x; shape] ->
      Var (CoqName.Name (Name.of_json x), Shape.of_json shape)
    | `List [`String "Typ"; x] -> Typ (CoqName.Name (Name.of_json x))
    | `List [`String "Descriptor"; x] ->
      Descriptor (CoqName.Name (Name.of_json x))
    | `List [`String "Constructor"; x] ->
      Constructor (CoqName.Name (Name.of_json x))
    | `List [`String "Field"; x] -> Field (CoqName.Name (Name.of_json x))
    | `List [`String "Include"; x] -> Include (PathName.of_json x)
    | `List [`String "Interface"; x; `List defs] ->
        Interface (CoqName.Name (Name.of_json x), List.map of_json defs)
    | _ -> raise (Error.Json
      "Expected a Var, Typ, Descriptor, Constructor, Field or Interface field.")

  let to_json_string (interface : t) : string =
    let pretty = pretty_format ~std:true (`Assoc [
      "version", `String "1";
      "content", to_json interface]) in
    let buffer = Buffer.create 0 in
    let formatter = Format.formatter_of_buffer buffer in
    Format.pp_set_margin formatter 120;
    Easy_format.Pretty.to_formatter formatter pretty;
    Format.pp_print_flush formatter ();
    Buffer.contents buffer
end

let rec to_json (interface : t) : json =
  match interface with
  | Var (x, shape) ->
    `List [`String "Var"; CoqName.to_json x; Shape.to_json shape]
  | Typ x -> `List [`String "Typ"; CoqName.to_json x]
  | Descriptor x -> `List [`String "Descriptor"; CoqName.to_json x]
  | Constructor x -> `List [`String "Constructor"; CoqName.to_json x]
  | Field x -> `List [`String "Field"; CoqName.to_json x]
  | Include x -> `List [`String "Include"; PathName.to_json x]
  | Interface (x, defs) ->
    `List [`String "Interface"; CoqName.to_json x; `List (List.map to_json defs)]

let rec of_json (json : json) : t =
  match json with
  | `List [`String "Var"; x; shape] ->
    Var (CoqName.of_json x, Shape.of_json shape)
  | `List [`String "Typ"; x] -> Typ (CoqName.of_json x)
  | `List [`String "Descriptor"; x] -> Descriptor (CoqName.of_json x)
  | `List [`String "Constructor"; x] -> Constructor (CoqName.of_json x)
  | `List [`String "Field"; x] -> Field (CoqName.of_json x)
  | `List [`String "Include"; x] -> Include (PathName.of_json x)
  | `List [`String "Interface"; x; `List defs] ->
      Interface (CoqName.of_json x, List.map of_json defs)
  | _ -> raise (Error.Json
    "Expected a Var, Typ, Descriptor, Constructor, Field or Interface field.")

let to_json_string (interface : t) : string =
  let pretty = pretty_format ~std:true (`Assoc [
    "version", `String "1";
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
    | `String "1" -> Version1.of_json @@ List.assoc "content" jsons
    | `String "2" -> of_json @@ List.assoc "content" jsons
    | _ -> raise (Error.Json "Wrong interface version, expected 1."))
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

let load_module (module_name : Name.t) (env : Effect.Type.t FullEnvi.t)
  : Effect.Type.t FullEnvi.t =
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
