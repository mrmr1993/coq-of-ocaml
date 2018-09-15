open SmartPrint
open Types

type t =
| Value of Loc.t * CoqName.t * Name.t list * Type.t
| TypeDefinition of Loc.t * TypeDefinition.t
| Module of Loc.t * CoqName.t * t list
| ModType of Loc.t * CoqName.t * t list

let rec pps (decls : t list) : SmartPrint.t =
  separate (newline ^^ newline) (List.map pp decls)

and pp (decl : t) : SmartPrint.t =
  match decl with
  | Value (loc, name, typ_vars, typ) ->
    group (Loc.pp loc ^^ !^ "Value" ^^ OCaml.tuple
      [CoqName.pp name; OCaml.list Name.pp typ_vars; Type.pp typ])
  | TypeDefinition (loc, typ_def) ->
    group (Loc.pp loc ^^ TypeDefinition.pp typ_def)
  | Module (loc, name, decls) ->
    nest (
      Loc.pp loc ^^ !^ "Module" ^^ CoqName.pp name ^-^ !^ ":" ^^ newline ^^
      indent (pps decls))
  | ModType (loc, name, decls) ->
    nest (
      Loc.pp loc ^^ !^ "Module Type" ^^ CoqName.pp name ^-^ !^ ":" ^^
      newline ^^ indent (pps decls))

let rec of_ocaml (env : unit FullEnvi.t) (signature : signature)
  : unit FullEnvi.t * t list =
  let of_signature_item (env : unit FullEnvi.t) (item : signature_item)
    : unit FullEnvi.t * t =
    match item with
    | Sig_value (name, { val_type = typ; val_loc = loc }) ->
      let loc = Loc.of_location loc in
      let (name, _, env) = FullEnvi.Var.create (Name.of_ident name) () env in
      let (typ, _, new_typ_vars) =
        Type.of_type_expr_new_typ_vars env loc Name.Map.empty typ in
      (env, Value (loc, name, Name.Set.elements new_typ_vars, typ))
    | Sig_type (name, typ, _) ->
      let loc = Loc.of_location typ.type_loc in
      let typ = TypeDefinition.of_declaration env loc name typ in
      let env = TypeDefinition.update_env typ env in
      (env, TypeDefinition (loc, typ))
    | Sig_module (name, { md_type = Mty_signature signature; md_loc = loc }, _) ->
      let loc = Loc.of_location loc in
      let name = Name.of_ident name in
      let (name, _, _) = FullEnvi.Module.create name (Mod.empty None []) env in
      let env = FullEnvi.enter_module name env in
      let (env, signatures) = of_ocaml env signature in
      let env = FullEnvi.leave_module (fun _ _ -> ()) env in
      (env, Module (loc, name, signatures))
    | Sig_module (name, { md_loc = loc }, _) ->
      let loc = Loc.of_location loc in
      Error.raise loc "This kind of module is not handled."
    | Sig_modtype (name, {mtd_type = Some (Mty_signature signature);
        mtd_loc = loc }) ->
      let loc = Loc.of_location loc in
      let name = Name.of_ident name in
      let (name, _, _) = FullEnvi.Module.create name (Mod.empty None []) env in
      let env = FullEnvi.enter_module name env in
      let (env, signatures) = of_ocaml env signature in
      let env = FullEnvi.leave_signature env in
      (env, ModType (loc, name, signatures))
    | Sig_modtype (name, { mtd_loc = loc }) ->
      let loc = Loc.of_location loc in
      Error.raise loc "This kind of module type is not handled."
    | Sig_typext (_, { ext_loc = loc }, _) ->
      let loc = Loc.of_location loc in
      Error.raise loc "Signature item `typext` not handled."
    | Sig_class (_, { cty_loc = loc }, _) ->
      let loc = Loc.of_location loc in
      Error.raise loc "Signature item `class` not handled."
    | Sig_class_type (_, { clty_loc = loc}, _) ->
      let loc = Loc.of_location loc in
       Error.raise loc "Signature item `class_type` not handled." in
  let (env, decls) =
    List.fold_left (fun (env, decls) item ->
      let (env, decl) = of_signature_item env item in
      (env, decl :: decls))
    (env, []) signature in
  let decls = List.rev decls in
  (env, decls)

let rec update_env (decls : t list) (a : 'a) (env : 'a FullEnvi.t)
  : 'a FullEnvi.t =
  let rec update_env_one (env : 'a FullEnvi.t) (decl : t) =
    match decl with
    | Value (loc, name, typ_vars, typ) -> FullEnvi.Var.assoc name a env
    | TypeDefinition (loc, typ_def) -> TypeDefinition.update_env typ_def env
    | Module (loc, name, decls) ->
      env |> FullEnvi.enter_module name
        |> update_env decls a
        |> FullEnvi.leave_module (fun _ v -> v)
    | ModType (loc, name, decls) ->
      env |> FullEnvi.enter_module name
        |> update_env decls a
        |> FullEnvi.leave_signature in
  List.fold_left update_env_one env decls

let rec to_coq (decls : t list) : SmartPrint.t =
  let to_coq_one (decl : t) : SmartPrint.t =
    match decl with
    | Value (_, name, typ_vars, typ) ->
      group (!^ "Parameter" ^^ CoqName.to_coq name ^^ !^ ":"  ^^
      (match typ_vars with
      | [] -> empty
      | _ :: _ -> !^ "forall" ^^
        braces (group (separate space (List.map Name.to_coq typ_vars) ^^
        !^ ":" ^^ !^ "Type")) ^-^ !^ ",") ^^
      Type.to_coq false typ ^-^ !^ ".") ^^
      begin match typ_vars with
      | [] -> empty
      | _ :: _ -> newline ^^ !^ "Arguments" ^^ CoqName.to_coq name ^^
        group (separate space
          (List.map (fun name -> braces @@ Name.to_coq name) typ_vars)) ^-^
        !^ "."
      end
    | TypeDefinition (_, typ_def) -> TypeDefinition.to_coq typ_def
    | Module (_, name, decls) ->
      nest (
        !^ "Module" ^^ CoqName.to_coq name ^-^ !^ "." ^^ newline ^^
        indent (to_coq decls) ^^ newline ^^
        !^ "End" ^^ CoqName.to_coq name ^-^ !^ ".")
    | ModType (_, name, decls) ->
      nest (
        !^ "Module Type" ^^ CoqName.to_coq name ^-^ !^ "." ^^ newline ^^
        indent (to_coq decls) ^^ newline ^^
        !^ "End" ^^ CoqName.to_coq name ^-^ !^ ".") in
  separate (newline ^^ newline) (List.map to_coq_one decls)
