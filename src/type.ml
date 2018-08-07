(** A type, with free type variables for polymorphic arguments. *)
open Types
open SmartPrint

type t =
  | Variable of Name.t
  | Arrow of t * t
  | Tuple of t list
  | Apply of BoundName.t * t list
  | Monad of Effect.Descriptor.t * t

let rec pp (typ : t) : SmartPrint.t =
  match typ with
  | Variable x -> Name.pp x
  | Arrow (typ1, typ2) -> nest @@ parens (pp typ1 ^^ !^ "->" ^^ pp typ2)
  | Tuple typs -> nest @@ parens (separate (space ^^ !^ "*" ^^ space) (List.map pp typs))
  | Apply (x, typs) ->
    nest (!^ "Type" ^^ nest (parens (
      separate (!^ "," ^^ space) (BoundName.pp x :: List.map pp typs))))
  | Monad (d, typ) -> nest (!^ "Monad" ^^ OCaml.tuple [
    Effect.Descriptor.pp d; pp typ])

(** Import an OCaml type. Add to the environment all the new free type variables. *)
let rec of_type_expr_new_typ_vars (env : 'a FullEnvi.t) (loc : Loc.t)
  (typ_vars : Name.t Name.Map.t) (typ : Types.type_expr)
  : t * Name.t Name.Map.t * Name.Set.t =
  match typ.desc with
  | Tvar _ ->
    let x = Printf.sprintf "A%d" typ.id in
    let (typ_vars, new_typ_vars, name) =
      if Name.Map.mem x typ_vars then (
        let name = Name.Map.find x typ_vars in
        (typ_vars, Name.Set.empty, name)
      ) else (
        let n = Name.Map.cardinal typ_vars in
        let name = if n < 25 then
            String.make 1 (Char.chr (Char.code 'A' + n))
          else (* We've used all the capital letters, switch to A1.. *)
            Printf.sprintf "A%d" (n-24) in
        let typ_vars = Name.Map.add x name typ_vars in
        (typ_vars, Name.Set.singleton name, name)) in
    let typ = Variable name in
    (typ, typ_vars, new_typ_vars)
  | Tarrow (_, typ_x, typ_y, _) ->
    let (typ_x, typ_vars, new_typ_vars_x) = of_type_expr_new_typ_vars env loc typ_vars typ_x in
    let (typ_y, typ_vars, new_typ_vars_y) = of_type_expr_new_typ_vars env loc typ_vars typ_y in
    (Arrow (typ_x, typ_y), typ_vars, Name.Set.union new_typ_vars_x new_typ_vars_y)
  | Ttuple typs ->
    let (typs, typ_vars, new_typ_vars) = of_typs_exprs_new_free_vars env loc typ_vars typs in
    (Tuple typs, typ_vars, new_typ_vars)
  | Tconstr (path, typs, _) ->
    let (typs, typ_vars, new_typ_vars) = of_typs_exprs_new_free_vars env loc typ_vars typs in
    let x = FullEnvi.Typ.bound loc (PathName.of_type_path loc path) env in
    (Apply (x, typs), typ_vars, new_typ_vars)
  | Tlink typ -> of_type_expr_new_typ_vars env loc typ_vars typ
  | Tpoly (typ, []) -> of_type_expr_new_typ_vars env loc typ_vars typ
  | _ ->
    Error.warn loc "Type not handled.";
    (Variable "unhandled_type", typ_vars, Name.Set.empty)

and of_typs_exprs_new_free_vars (env : 'a FullEnvi.t) (loc : Loc.t)
  (typ_vars : Name.t Name.Map.t) (typs : Types.type_expr list)
  : t list * Name.t Name.Map.t * Name.Set.t =
  let (typs, typ_vars, new_typ_vars) =
    List.fold_left (fun (typs, typ_vars, new_typ_vars) typ ->
      let (typ, typ_vars, new_typ_vars') = of_type_expr_new_typ_vars env loc typ_vars typ in
      (typ :: typs, typ_vars, Name.Set.union new_typ_vars new_typ_vars'))
      ([], typ_vars, Name.Set.empty) typs in
  (List.rev typs, typ_vars, new_typ_vars)

let rec of_type_expr ?allow_anon:(anon_var=false) (env : 'a FullEnvi.t)
  (loc : Loc.t) (typ : Types.type_expr) : t =
  match typ.desc with
  | Tvar (Some x) -> Variable x
  | Tarrow (_, typ_x, typ_y, _) ->
    Arrow (of_type_expr ~allow_anon:anon_var env loc typ_x,
     of_type_expr ~allow_anon:anon_var env loc typ_y)
  | Ttuple typs ->
    Tuple (List.map (of_type_expr ~allow_anon:anon_var env loc) typs)
  | Tconstr (path, typs, _) ->
    let x = FullEnvi.Typ.bound loc (PathName.of_type_path loc path) env in
    Apply (x, List.map (of_type_expr ~allow_anon:anon_var env loc) typs)
  | Tlink typ -> of_type_expr ~allow_anon:anon_var env loc typ
  | Tpoly (typ, []) -> of_type_expr ~allow_anon:anon_var env loc typ
  | Tvar None when anon_var -> Variable "_"
  | _ ->
    Error.warn loc "Type not handled.";
    Variable "unhandled_type"

let of_type_expr_variable (loc : Loc.t) (typ : Types.type_expr) : Name.t =
  match typ.desc with
  | Tvar (Some x) -> x
  | _ ->
    Error.warn loc "The type parameter was expected to be a variable.";
    "expected_a_type_variable"

let rec type_effects (env : Effect.Type.t FullEnvi.t) (typ : t)
  : Effect.Type.t =
  match typ with
  | Variable x -> Effect.Type.Pure
  | Arrow (typ1, typ2) ->
    Effect.Type.union (List.map (type_effects env) [typ1; typ2])
  | Tuple typs -> Effect.Type.union (List.map (type_effects env) typs)
  | Apply (x, typs) ->
    Effect.Type.union (FullEnvi.Typ.find x env Effect.Type.depth_lift ::
      List.map (type_effects env) typs)
  | Monad (x, typ) -> type_effects env typ

let is_function (typ : t) : bool =
  match typ with
  | Arrow _ -> true
  | _ -> false

let rec pure_type (typ : t) : Effect.PureType.t =
  match typ with
  | Variable x -> Effect.PureType.Variable x
  | Arrow (typ1, typ2) ->
    Effect.PureType.Arrow (pure_type typ1, pure_type typ2)
  | Tuple typs -> Effect.PureType.Tuple (List.map pure_type typs)
  | Apply (x, typs) -> Effect.PureType.Apply (x, List.map pure_type typs)
  | Monad (x, typ) -> pure_type typ

let rec unify (ptyp : Effect.PureType.t) (typ : t)
  : Effect.PureType.t Name.Map.t =
  match ptyp, typ with
  | Effect.PureType.Variable x, _ ->
    Name.Map.singleton x (pure_type typ)
  | _, Monad (_, typ) -> unify ptyp typ
  | Effect.PureType.Arrow (ptyp1, ptyp2), Arrow (typ1, typ2) ->
    Name.Map.union (fun _ typ _ -> Some typ)
      (unify ptyp1 typ1) (unify ptyp2 typ2)
  | Effect.PureType.Tuple ptyps, Tuple typs ->
    List.fold_left2 (fun var_map ptyp typ ->
        Name.Map.union (fun _ typ _ -> Some typ) var_map (unify ptyp typ))
      Name.Map.empty ptyps typs
  | Effect.PureType.Apply (px, ptyps), Apply (x, typs) ->
    List.fold_left2 (fun var_map ptyp typ ->
        Name.Map.union (fun _ typ _ -> Some typ) var_map (unify ptyp typ))
      Name.Map.empty ptyps typs
  | _, _ -> failwith "Could not unify types"

let rec typ_args (typ : t) : Name.Set.t =
  match typ with
  | Variable x -> Name.Set.singleton x
  | Arrow (typ1, typ2) -> typ_args_of_typs [typ1; typ2]
  | Tuple typs | Apply (_, typs) -> typ_args_of_typs typs
  | Monad (_, typ) -> typ_args typ

and typ_args_of_typs (typs : t list) : Name.Set.t =
  List.fold_left (fun args typ -> Name.Set.union args (typ_args typ))
    Name.Set.empty typs

(** In a function's type extract the body's type (up to [n] arguments). *)
let rec open_type (typ : t) (n : int) : t list * t =
  if n = 0 then
    ([], typ)
  else
    match typ with
    | Arrow (typ1, typ2) ->
      let (typs, typ) = open_type typ2 (n - 1) in
      (typ1 :: typs, typ)
    | _ -> failwith "Expected an arrow type."

let monadise (typ : t) (effect : Effect.t) : t =
  let rec aux (typ : t) (effect_typ : Effect.Type.t) : t =
    match (typ, effect_typ) with
    | (Variable _, Effect.Type.Pure) | (Tuple _, Effect.Type.Pure)
      | (Apply _, Effect.Type.Pure) | (Arrow _, Effect.Type.Pure) -> typ
    | (Arrow (typ1, typ2), Effect.Type.Arrow (d, effect_typ2)) ->
      let typ2 = aux typ2 effect_typ2 in
      Arrow (typ1,
        if Effect.Descriptor.is_pure d then
          typ2
        else
          Monad (d, typ2))
    | (Monad _, _) -> failwith "This type is already monadic."
    | _ -> failwith "Type and effect type are not compatible." in
  let typ = aux typ effect.Effect.typ in
  if Effect.Descriptor.is_pure effect.Effect.descriptor then
    typ
  else
    Monad (effect.Effect.descriptor, typ)

(** Pretty-print a type (inside parenthesis if the [paren] flag is set). *)
let rec to_coq (paren : bool) (typ : t) : SmartPrint.t =
  match typ with
  | Variable x -> Name.to_coq x
  | Arrow (typ_x, typ_y) ->
    Pp.parens paren @@ nest (to_coq true typ_x ^^ !^ "->" ^^ to_coq false typ_y)
  | Tuple typs ->
    (match typs with
    | [] -> !^ "unit"
    | _ ->
      Pp.parens paren @@ nest @@ separate (space ^^ !^ "*" ^^ space)
        (List.map (to_coq true) typs))
  | Apply (path, typs) ->
    Pp.parens (paren && typs <> []) @@ nest @@ separate space
      (BoundName.to_coq path :: List.map (to_coq true) typs)
  | Monad (d, typ) ->
    Pp.parens paren @@ nest (
      !^ "M" ^^ Effect.Descriptor.to_coq d ^^ to_coq true typ)
