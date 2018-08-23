(** A structure represents the contents of a ".ml" file. *)
open Typedtree
open SmartPrint

(** A value is a toplevel definition made with a "let". *)
module Value = struct
  type 'a t = 'a Exp.t Exp.Definition.t

  let pp (pp_a : 'a -> SmartPrint.t) (value : 'a t) : SmartPrint.t =
    nest (!^ "Value" ^^ Exp.Definition.pp (Exp.pp pp_a) value)

  (** Pretty-print a value definition to Coq. *)
  let to_coq (value : 'a t) : SmartPrint.t =
    let firt_case = ref true in
    separate (newline ^^ newline) (value.Exp.Definition.cases |> List.map (fun (header, e) ->
      nest (
        (if !firt_case then (
          firt_case := false;
          if Recursivity.to_bool value.Exp.Definition.is_rec then
            !^ "Fixpoint"
          else
            !^ "Definition"
        ) else
          !^ "with") ^^
        CoqName.to_coq header.Exp.Header.name ^^
        (match header.Exp.Header.typ_vars with
        | [] -> empty
        | _ :: _ ->
          braces @@ group (separate space (List.map Name.to_coq header.Exp.Header.typ_vars) ^^
          !^ ":" ^^ !^ "Type")) ^^
        group (separate space (header.Exp.Header.implicit_args
          |> List.map (fun (x, x_typ) ->
            braces (CoqName.to_coq x ^^ !^ ":" ^^ Type.to_coq false x_typ)))) ^^
        group (separate space (header.Exp.Header.args |> List.map (fun (x, t) ->
          parens @@ nest (CoqName.to_coq x ^^ !^ ":" ^^ Type.to_coq false t)))) ^^
        !^ ": " ^-^ Type.to_coq false header.Exp.Header.typ ^-^
        !^ " :=" ^^ Exp.to_coq false e))) ^-^ !^ "."
end

(** A structure. *)
type 'a t =
  | Require of Name.t list (* These should begin the structure to satisfy Coq. *)
  | Value of Loc.t * 'a Value.t
  | Primitive of Loc.t * PrimitiveDeclaration.t
  | TypeDefinition of Loc.t * TypeDefinition.t
  | Exception of Loc.t * Exception.t
  | Reference of Loc.t * 'a Reference.t
  | Open of Loc.t * Open.t
  | Include of Loc.t * Include.t
  | Module of Loc.t * Name.t * 'a t list

let rec pps (pp_a : 'a -> SmartPrint.t) (defs : 'a t list) : SmartPrint.t =
  separate (newline ^^ newline) (List.map (pp pp_a) defs)

and pp (pp_a : 'a -> SmartPrint.t) (def : 'a t) : SmartPrint.t =
  match def with
  | Require names -> group (!^ "Require" ^^ OCaml.list Name.pp names)
  | Value (loc, value) ->
    group (Loc.pp loc ^^ Value.pp pp_a value)
  | Primitive (loc, prim) ->
    group (Loc.pp loc ^^ PrimitiveDeclaration.pp prim)
  | TypeDefinition (loc, typ_def) ->
    group (Loc.pp loc ^^ TypeDefinition.pp typ_def)
  | Exception (loc, exn) -> group (Loc.pp loc ^^ Exception.pp exn)
  | Reference (loc, r) -> group (Loc.pp loc ^^ Reference.pp pp_a r)
  | Open (loc, o) -> group (Loc.pp loc ^^ Open.pp o)
  | Include (loc, name) -> group (Loc.pp loc ^^ Include.pp name)
  | Module (loc, name, defs) ->
    nest (
      Loc.pp loc ^^ !^ "Module" ^^ Name.pp name ^-^ !^ ":" ^^ newline ^^
      indent (pps pp_a defs))

(** Import an OCaml structure. *)
let rec of_structure (env : unit FullEnvi.t) (structure : structure)
  : unit FullEnvi.t * (Loc.t * Type.t) t list =
  let of_structure_item (env : unit FullEnvi.t) (item : structure_item)
    : unit FullEnvi.t * (Loc.t * Type.t) t =
    let loc = Loc.of_location item.str_loc in
    match item.str_desc with
    | Tstr_value (_, cases) when Reference.is_reference loc cases ->
      let r = Reference.of_ocaml env loc cases in
      let (env, r) = Reference.update_env (fun _ exp -> exp) r env in
      (env, Reference (loc, r))
    | Tstr_value (is_rec, cases) ->
      let (env, def) =
        Exp.import_let_fun env loc Name.Map.empty is_rec cases in
      (env, Value (loc, def))
    | Tstr_type (_, typs) ->
      let def = TypeDefinition.of_ocaml env loc typs in
      let env = TypeDefinition.update_env def () env in
      (env, TypeDefinition (loc, def))
    | Tstr_exception exn ->
      let exn = Exception.of_ocaml env loc exn in
      let env = Exception.update_env exn env in
      (env, Exception (loc, exn))
    | Tstr_open { open_path = path } ->
      let o = Open.of_ocaml env loc path in
      let env = Open.update_env loc o env in
      (env, Open (loc, o))
    | Tstr_include { incl_mod = { mod_desc = Tmod_ident (path, _) } } ->
      let incl = Include.of_ocaml env loc path in
      let env = Include.update_env loc incl env in
      (env, Include (loc, incl))
    | Tstr_include _ -> Error.raise loc "This kind of include is not handled"
    | Tstr_module {mb_id = name;
      mb_expr = { mod_desc = Tmod_structure structure }}
    | Tstr_module {mb_id = name;
      mb_expr = { mod_desc =
        Tmod_constraint ({ mod_desc = Tmod_structure structure }, _, _, _) }} ->
      let name = Name.of_ident name in
      let env = FullEnvi.enter_module (CoqName.Name name) env in
      let (env, structures) = of_structure env structure in
      let env = FullEnvi.leave_module (fun _ _ -> ()) (fun _ _ -> ()) env in
      (env, Module (loc, name, structures))
    | Tstr_modtype _ -> Error.raise loc "Signatures not handled."
    | Tstr_module { mb_expr = { mod_desc = Tmod_functor _ }} ->
      Error.raise loc "Functors not handled."
    | Tstr_module _ -> Error.raise loc "This kind of module is not handled."
    | Tstr_eval _ -> Error.raise loc "Structure item `eval` not handled."
    | Tstr_primitive val_desc ->
      let prim = PrimitiveDeclaration.of_ocaml env loc val_desc in
      let env = PrimitiveDeclaration.update_env prim env in
      (env, Primitive (loc, prim))
    | Tstr_typext _ -> Error.raise loc "Structure item `typext` not handled."
    | Tstr_recmodule _ -> Error.raise loc "Structure item `recmodule` not handled."
    | Tstr_class _ -> Error.raise loc "Structure item `class` not handled."
    | Tstr_class_type _ -> Error.raise loc "Structure item `class_type` not handled."
    | Tstr_attribute _ -> Error.raise loc "Structure item `attribute` not handled." in
  let (env, defs) =
    List.fold_left (fun (env, defs) item ->
      (* We ignore attribute items. *)
      match item.str_desc with
      | Tstr_attribute _ -> (env, defs)
      | _ ->
        let (env, def) = of_structure_item env item in
        (env, def :: defs))
    (env, []) structure.str_items in
  let requires = FullEnvi.requires env in
  let defs = List.rev defs in
  let defs = if requires == [] then defs else Require requires :: defs in
  (env, defs)

let rec monadise_let_rec (env : unit FullEnvi.t)
  (defs : (Loc.t * Type.t) t list)
  : unit FullEnvi.t * (Loc.t * Type.t) t list =
  let monadise_let_rec_one (env : unit FullEnvi.t) (def : (Loc.t * Type.t) t)
    : unit FullEnvi.t * (Loc.t * Type.t) t list =
    match def with
    | Require _ -> (env, [def])
    | Value (loc, def) ->
      let (env, defs) = Exp.monadise_let_rec_definition env def in
      (env, defs |> List.rev |> List.map (fun def -> Value (loc, def)))
    | Primitive (loc, prim) ->
      (PrimitiveDeclaration.update_env prim env, [def])
    | TypeDefinition (loc, typ_def) ->
      (TypeDefinition.update_env typ_def () env, [def])
    | Exception (loc, exn) -> (Exception.update_env exn env, [def])
    | Reference (loc, r) ->
      let (env, r) = Reference.update_env Exp.monadise_let_rec r env in
      (env, [Reference (loc, r)])
    | Open (loc, o) -> (Open.update_env loc o env, [def])
    | Include (loc, name) ->
      (Include.update_env loc name env, [def])
    | Module (loc, name, defs) ->
      let env = FullEnvi.enter_module (CoqName.Name name) env in
      let (env, defs) = monadise_let_rec env defs in
      let env = FullEnvi.leave_module (fun _ _ -> ()) (fun _ _ -> ()) env in
      (env, [Module (loc, name, defs)]) in
  let (env, defs) = List.fold_left (fun (env, defs) def ->
    let (env, defs') = monadise_let_rec_one env def in
    (env, defs' @ defs))
    (env, []) defs in
  (env, List.rev defs)

let rec effects (env : Effect.Type.t FullEnvi.t) (defs : ('a * Type.t) t list)
  : Effect.Type.t FullEnvi.t * ('a * Effect.t) t list =
  let effects_one (env : Effect.Type.t FullEnvi.t) (def : ('a * Type.t) t)
    : Effect.Type.t FullEnvi.t * ('a * Effect.t) t =
    match def with
    | Require names -> (env, Require names)
    | Value (loc, def) ->
      let def = Exp.effects_of_def env def in
      (if def.Exp.Definition.cases |> List.exists (fun (header, e) ->
        header.Exp.Header.args = [] &&
          not (Effect.Descriptor.is_pure (snd (Exp.annotation e)).Effect.descriptor)) then
        Error.warn loc "Toplevel effects are forbidden.");
      let env = Exp.env_after_def_with_effects env def in
      (env, Value (loc, def))
    | Primitive (loc, prim) ->
      (PrimitiveDeclaration.update_env_with_effects prim env, Primitive (loc, prim))
    | TypeDefinition (loc, typ_def) ->
      (TypeDefinition.update_env typ_def Effect.Type.Pure env,
       TypeDefinition (loc, typ_def))
    | Exception (loc, exn) ->
      (Exception.update_env_with_effects exn env, Exception (loc, exn))
    | Reference (loc, r) ->
      let (env, r) = Reference.update_env_with_effects r env in
      (env, Reference (loc, r))
    | Open (loc, o) -> (Open.update_env loc o env, Open (loc, o))
    | Include (loc, name) ->
      (Include.update_env loc name env, Include (loc, name))
    | Module (loc, name, defs) ->
      let env = FullEnvi.enter_module (CoqName.Name name) env in
      let (env, defs) = effects env defs in
      let env = FullEnvi.leave_module Effect.Type.leave_prefix
        Effect.Type.resolve_open env in
      (env, Module (loc, name, defs)) in
  let (env, defs) =
    List.fold_left (fun (env, defs) def ->
      let (env, def) =
        effects_one env def in
      (env, def :: defs))
      (env, []) defs in
  (env, List.rev defs)

let rec monadise (env : unit FullEnvi.t) (defs : (Loc.t * Effect.t) t list)
  : unit FullEnvi.t * Loc.t t list =
  let monadise_one (env : unit FullEnvi.t) (def : (Loc.t * Effect.t) t)
    : unit FullEnvi.t * Loc.t t =
    match def with
    | Require names -> (env, Require names)
    | Value (loc, def) ->
      let env_in_def = Exp.Definition.env_in_def def env in
      let def = { def with
        Exp.Definition.cases =
          def.Exp.Definition.cases |> List.map (fun (header, e) ->
            let typ = Type.monadise header.Exp.Header.typ (snd (Exp.annotation e)) in
        let header = { header with Exp.Header.typ = typ } in
        let env = Exp.Header.env_in_header header env_in_def () in
        let e = Exp.monadise env e in
        (header, e)) } in
      let env = Exp.Definition.env_after_def def env in
      (env, Value (loc, def))
    | Primitive (loc, prim) ->
      (PrimitiveDeclaration.update_env prim env, Primitive (loc, prim))
    | TypeDefinition (loc, typ_def) ->
      (TypeDefinition.update_env typ_def () env, TypeDefinition (loc, typ_def))
    | Exception (loc, exn) ->
      (Exception.update_env exn env, Exception (loc, exn))
    | Reference (loc, r) ->
      let (env, r) = Reference.update_env Exp.monadise r env in
      (env, Reference (loc, r))
    | Open (loc, o) -> (* Don't update the environment; it likely doesn't contain our module *)
      (env, Open (loc, o))
    | Include (loc, name) -> (* Don't update the environment; it likely doesn't contain our module *)
      (env, Include (loc, name))
    | Module (loc, name, defs) ->
      let (env, defs) = monadise (FullEnvi.enter_module (CoqName.Name name) env) defs in
      let env = FullEnvi.leave_module (fun _ _ -> ()) (fun _ _ -> ()) env in
      (env, Module (loc, name, defs)) in
  let (env, defs) =
    List.fold_left (fun (env, defs) def ->
      let (env_units, def) = monadise_one env def in
      (env, def :: defs))
      (env, []) defs in
  (env, List.rev defs)

(** Pretty-print a structure to Coq. *)
let rec to_coq (defs : 'a t list) : SmartPrint.t =
  let to_coq_one (def : 'a t) : SmartPrint.t =
    match def with
    | Require names ->
      group (!^ "Require" ^^ separate space (List.map Name.pp names) ^-^ !^ ".")
    | Value (_, value) -> Value.to_coq value
    | Primitive (_, prim) -> PrimitiveDeclaration.to_coq prim
    | TypeDefinition (_, typ_def) -> TypeDefinition.to_coq typ_def
    | Exception (_, exn) -> Exception.to_coq exn
    | Reference (_, r) -> Reference.to_coq r
    | Open (_, o) -> Open.to_coq o
    | Include (_, incl) -> Include.to_coq incl
    | Module (_, name, defs) ->
      nest (
        !^ "Module" ^^ Name.to_coq name ^-^ !^ "." ^^ newline ^^
        indent (to_coq defs) ^^ newline ^^
        !^ "End" ^^ Name.to_coq name ^-^ !^ ".") in
  separate (newline ^^ newline) (List.map to_coq_one defs)
