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

  let to_effect_typ (shape : t) : Effect.Type.t =
    let descriptor ds : Effect.Descriptor.t =
      let ds = ds |> List.map (fun d ->
        let bound_descriptor = { BoundName.full_path = d; local_path = d } in
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
  | Var of CoqName.t * Effect.t
  | Typ of CoqName.t
  | Descriptor of CoqName.t
  | Exception of CoqName.t * CoqName.t
  | Constructor of CoqName.t * Effect.PureType.t list
  | Field of CoqName.t * Effect.PureType.t
  | Include of PathName.t
  | Interface of CoqName.t * t list
  | Signature of CoqName.t * t list

let rec pp (interface : t) : SmartPrint.t =
  match interface with
  | Var (x, shape) ->
    !^ "Var" ^^ OCaml.tuple [CoqName.pp x; Effect.pp shape]
  | Typ x -> !^ "Typ" ^^ CoqName.pp x
  | Descriptor x -> !^ "Descriptor" ^^ CoqName.pp x
  | Exception (x, raise_name) ->
    !^ "Exception" ^^ OCaml.tuple [CoqName.pp x; CoqName.pp raise_name]
  | Constructor (x, typ) ->
    !^ "Constructor" ^^ CoqName.pp x ^^ OCaml.list Effect.PureType.pp typ
  | Field (x, typ) ->
    !^ "Field" ^^ CoqName.pp x ^^ !^ ":" ^^ Effect.PureType.pp typ
  | Include x -> !^ "Include" ^^ PathName.pp x
  | Interface (x, defs) ->
    !^ "Interface" ^^ CoqName.pp x ^^ !^ "=" ^^ newline ^^ indent
      (separate newline (List.map pp defs))
  | Signature (x, defs) ->
    !^ "Signature" ^^ CoqName.pp x ^^ !^ "=" ^^ newline ^^ indent
      (separate newline (List.map pp defs))

let of_typ_definition (typ_def : TypeDefinition.t) : t list =
  match typ_def with
  | TypeDefinition.Inductive (name, _, constructors) ->
    Typ name ::
    List.map (fun (x, typs) -> Constructor (x, List.map Type.pure_type typs))
      constructors
  | TypeDefinition.Record (name, _, fields) ->
    Typ name :: List.map (fun (x, typ) -> Field (x, Type.pure_type typ)) fields
  | TypeDefinition.Synonym (name, _, _) | TypeDefinition.Abstract (name, _) ->
    [Typ name]

let rec of_signatures (decls : Signature.t list) : t list =
  List.flatten (List.map of_signature decls)

and of_signature (decl : Signature.t) : t list =
  match decl with
  | Signature.Value (_, name, typ_vars, typ) -> [Var (name, Effect.pure)]
  | Signature.TypeDefinition (_, typ_def) -> of_typ_definition typ_def
  | Signature.Module (_, name, decls) ->
    [Interface (name, of_signatures decls)]
  | Signature.ModType (_, name, decls) ->
    [Signature (name, of_signatures decls)]

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
      Var (name, Effect.compress typ))
  | Structure.Primitive (_, prim) ->
    (* TODO: Update to reflect that primitives are not usually pure. *)
    [Var (prim.PrimitiveDeclaration.name, Effect.pure)]
  | Structure.TypeDefinition (_, typ_def) -> of_typ_definition typ_def
  | Structure.Exception (_, exn) ->
    [Exception (exn.Exception.name, exn.Exception.raise_name)]
  | Structure.Reference (_, r) ->
    [Descriptor r.Reference.state_name;
     Var (r.Reference.name, r.Reference.effect)]
  | Structure.Open _ -> []
  | Structure.Include (_, name) -> [Include name.local_path]
  | Structure.Module (_, name, defs) ->
    [Interface (name, of_structures defs)]
  | Structure.Signature (_, name, decls) ->
    [Signature (name, of_signatures decls)]

let rec to_full_envi (top_name : Name.t option) (interface : t)
  (env : Effect.t FullEnvi.t) : Effect.t FullEnvi.t =
  match interface with
  | Var (x, effect) ->
    let effect = match top_name with
      | None -> effect
      | Some top_name ->
        effect |> Effect.map (fun ({full_path} as bound_path) ->
          let full_path' = { full_path with
            PathName.path = top_name :: full_path.PathName.path } in
          let bound_path = if FullEnvi.has_global_value env full_path' then
              { BoundName.full_path = full_path'; local_path = full_path' }
            else bound_path in
          FullEnvi.localize (FullEnvi.has_value env) env bound_path) in
    FullEnvi.Var.assoc x effect env
  | Typ x -> FullEnvi.Typ.assoc x env
  | Descriptor x -> FullEnvi.Descriptor.assoc x env
  | Exception (name, raise_name) ->
    env |> Exception.update_env_with_effects
      { Exception.name; raise_name; typ = Type.Variable "_" }
  | Constructor (x, typs) -> FullEnvi.Constructor.assoc x typs env
  | Field (x, typ) -> FullEnvi.Field.assoc x typ env
  | Include x -> Include.of_interface x env
  | Interface (x, defs) ->
    let env = FullEnvi.enter_module x env in
    let env = List.fold_left (fun env def -> to_full_envi top_name def env) env
      defs in
    FullEnvi.leave_module FullEnvi.localize_effects env
  | Signature (x, decls) ->
    let env = FullEnvi.enter_module x env in
    let env = List.fold_left (fun env def -> to_full_envi top_name def env) env
      decls in
    FullEnvi.leave_signature env


let load_interface (coq_prefix : Name.t) (interface : t)
  (env : Effect.t FullEnvi.t) : Name.t * Effect.t FullEnvi.t =
  let name = match interface with
    | Interface (name, _) -> CoqName.ocaml_name name
    | _ -> "" in
  let coq_name = if coq_prefix == "" || name == "" then coq_prefix ^ name
    else coq_prefix ^ "." ^ name in
  let env = FullEnvi.enter_module (CoqName.of_names name coq_name) env in
  let env = match interface with
    | Interface (_, defs) ->
      List.fold_left (fun env def -> to_full_envi (Some coq_name) def env) env
        defs
    | _ -> to_full_envi (Some coq_name) interface env in
  (coq_name, FullEnvi.leave_module FullEnvi.localize_effects env)

module Version1 = struct
  let rec to_json (interface : t) : json =
    match interface with
    | Var (x, shape) ->
      let x = CoqName.ocaml_name x in
      let shape = Shape.of_effect_typ shape.Effect.typ in
      `List [`String "Var"; Name.to_json x; Shape.to_json shape]
    | Typ x ->
      let x = CoqName.ocaml_name x in
      `List [`String "Typ"; Name.to_json x]
    | Descriptor x ->
      let x = CoqName.ocaml_name x in
      `List [`String "Descriptor"; Name.to_json x]
    | Exception (name, raise_name) ->
      failwith "Cannot output exceptions in V1 interfaces. Please use a newer version."
    | Constructor (x, typs) ->
      let x = CoqName.ocaml_name x in
      `List [`String "Constructor"; Name.to_json x]
    | Field (x, typ) ->
      let x = CoqName.ocaml_name x in
      `List [`String "Field"; Name.to_json x]
    | Include x -> `List [`String "Include"; PathName.to_json x]
    | Interface (x, defs) ->
      let x = CoqName.ocaml_name x in
      `List [`String "Interface"; Name.to_json x; `List (List.map to_json defs)]
    | Signature _ ->
      failwith "Cannot output signatures in V1 interfaces. Please use a newer version."

  let rec of_json (json : json) : t =
    match json with
    | `List [`String "Var"; x; shape] ->
      Var (CoqName.Name (Name.of_json x),
        Effect.eff (Shape.to_effect_typ (Shape.of_json shape)))
    | `List [`String "Typ"; x] -> Typ (CoqName.Name (Name.of_json x))
    | `List [`String "Descriptor"; x] ->
      Descriptor (CoqName.Name (Name.of_json x))
    | `List [`String "Constructor"; x] ->
      Constructor (CoqName.Name (Name.of_json x), [])
    | `List [`String "Field"; x] ->
      Field (CoqName.Name (Name.of_json x), Effect.PureType.Variable "_")
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
  | Var (x, eff) ->
    `List [`String "Var"; CoqName.to_json x; Effect.to_json eff]
  | Typ x -> `List [`String "Typ"; CoqName.to_json x]
  | Descriptor x -> `List [`String "Descriptor"; CoqName.to_json x]
  | Exception (name, raise_name) ->
    `List [`String "Exception"; CoqName.to_json name; CoqName.to_json raise_name]
  | Constructor (x, typs) ->
    `List [`String "Constructor"; CoqName.to_json x;
      `List (List.map Effect.PureType.to_json typs)]
  | Field (x, typ) ->
    `List [`String "Field"; CoqName.to_json x; Effect.PureType.to_json typ]
  | Include x -> `List [`String "Include"; PathName.to_json x]
  | Interface (x, defs) ->
    `List [`String "Interface"; CoqName.to_json x; `List (List.map to_json defs)]
  | Signature (x, defs) ->
    `List [`String "Signature"; CoqName.to_json x; `List (List.map to_json defs)]

let rec of_json (json : json) : t =
  match json with
  | `List [`String "Var"; x; eff] ->
    Var (CoqName.of_json x, Effect.of_json eff)
  | `List [`String "Typ"; x] -> Typ (CoqName.of_json x)
  | `List [`String "Descriptor"; x] -> Descriptor (CoqName.of_json x)
  | `List [`String "Exception"; name; raise_name] ->
    Exception (CoqName.of_json name, CoqName.of_json raise_name)
  | `List [`String "Constructor"; x; `List typs] ->
    Constructor (CoqName.of_json x, List.map Effect.PureType.of_json typs)
  | `List [`String "Field"; x; typ] ->
    Field (CoqName.of_json x, Effect.PureType.of_json typ)
  | `List [`String "Include"; x] -> Include (PathName.of_json x)
  | `List [`String "Interface"; x; `List defs] ->
      Interface (CoqName.of_json x, List.map of_json defs)
  | `List [`String "Signature"; x; `List defs] ->
      Signature (CoqName.of_json x, List.map of_json defs)
  | _ -> raise (Error.Json
    "Expected a Var, Typ, Descriptor, Constructor, Field or Interface field.")

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

let load_module (module_name : Name.t) (env : Effect.t FullEnvi.t)
  : Effect.t FullEnvi.t =
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
