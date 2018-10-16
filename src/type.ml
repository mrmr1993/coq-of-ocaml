(** A type, with free type variables for polymorphic arguments. *)
open Types
open SmartPrint
open Yojson.Basic

include CommonType.Type
type t = typ

let pp (typ : t) : SmartPrint.t = CommonType.pp typ

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
    let typ = match FullEnvi.Typ.find loc x env with
      | Open _ -> OpenApply (x, typs, [])
      | _ -> Apply (x, typs) in
    (typ, typ_vars, new_typ_vars)
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

let is_function (typ : t) : bool =
  match typ with
  | Arrow _ -> true
  | _ -> false

let equal (typ1 : t) (typ2 : t) : bool = CommonType.equal typ1 typ2

let is_open (typ : t) : bool =
  match typ with
  | OpenApply _ -> true
  | _ -> false

let map_vars (f : Name.t -> t) (typ : t) : t = CommonType.map_vars f typ

let resolve (env : 'a FullEnvi.t) (typ : t) : t option =
  match typ with
  | Apply (x, typs) ->
    begin match FullEnvi.Typ.find Loc.Unknown x env with
    | CommonType.TypeDefinition.Synonym (_, typ_args, typ) ->
      let typ_map = List.fold_left2 (fun map name typ ->
        Name.Map.add name typ map) Name.Map.empty typ_args typs in
      let typ = typ |> map_vars (fun name ->
        match Name.Map.find_opt name typ_map with
        | Some typ -> typ
        | None -> Variable name) in
      Some typ
    | _ -> None
    end
  | _ -> None

let rec unify (env : 'a FullEnvi.t) (typ1 : t) (typ2 : t) : t Name.Map.t =
  let unify = unify env in
  let union = Name.Map.union (fun _ typ _ -> Some typ) in
  match typ1, typ2 with
  | Monad (_, typ), _ -> unify typ typ2
  | _, Monad (_, typ) -> unify typ1 typ
  | Variable x, _ -> Name.Map.singleton x typ2
  | Arrow (typ1a, typ1b), Arrow (typ2a, typ2b) ->
    union (unify typ1a typ2a) (unify typ1b typ2b)
  | Tuple typs1, Tuple typs2 ->
    List.fold_left2 (fun var_map typ1 typ2 -> union var_map (unify typ1 typ2))
      Name.Map.empty typs1 typs2
  | Apply (x1, typs1), Apply (x2, typs2)
    when BoundName.stable_compare x1 x2 = 0 ->
    List.fold_left2 (fun var_map typ1 typ2 -> union var_map (unify typ1 typ2))
      Name.Map.empty typs1 typs2
  | Apply _, Apply _ ->
    begin match resolve env typ1, resolve env typ2 with
    | Some typ1, Some typ2 -> unify typ1 typ2
    | Some typ1, None -> unify typ1 typ2
    | None, Some typ2 -> unify typ1 typ2
    | None, None -> failwith "Could not unify type names."
    end
  | OpenApply (x1, typs1, typ_defs1), OpenApply (x2, typs2, typ_defs2) ->
    List.fold_left2 (fun var_map typ1 typ2 ->
        union var_map (unify typ1 typ2))
      Name.Map.empty typs1 typs2
  | _, _ -> failwith "Could not unify types"

let rec unify_monad (env : 'a FullEnvi.t) (f : desc -> desc option -> desc)
  (typ1 : t) (typ2 : t) : t =
  let unify_monad = unify_monad env f in
  match typ1, typ2 with
  | Arrow (typ1a, typ1b), Arrow (typ2a, typ2b) ->
    Arrow (unify_monad typ1a typ2a, unify_monad typ1b typ2b)
  | Tuple typs1, Tuple typs2 ->
    Tuple (List.map2 unify_monad typs1 typs2)
  | Tuple [],
    Apply ({ BoundName.full_path = { PathName.path = []; base = "unit" } }, [])
  | Apply ({ BoundName.full_path = { PathName.path = []; base = "unit" } }, []),
    Tuple [] -> typ1
  | Apply (x1, typs1), Apply (x2, typs2)
    when BoundName.stable_compare x1 x2 = 0 ->
    Apply (x1, List.map2 unify_monad typs1 typs2)
  | Apply _, Apply _ ->
    begin match resolve env typ1, resolve env typ2 with
    | Some typ1, Some typ2 -> unify_monad typ1 typ2
    | Some typ1, None -> unify_monad typ1 typ2
    | None, Some typ2 -> unify_monad typ1 typ2
    | None, None -> failwith "Could not unify type names."
    end
  | Monad (d1, typ1), Monad (d2, typ2) ->
    Monad (f d1 (Some d2), unify_monad typ1 typ2)
  | Monad (d, typ1), typ2 | typ1, Monad (d, typ2) ->
    Monad (f d None, unify_monad typ1 typ2)
  | OpenApply (x1, typs1, typ_defs1), OpenApply (x2, typs2, typ_defs2) ->
    let typ_defs = BoundName.Set.elements @@ BoundName.Set.union
      (BoundName.Set.of_list typ_defs1) (BoundName.Set.of_list typ_defs2) in
    OpenApply (x1, List.map2 unify_monad typs1 typs2, typ_defs)
  | _, Variable y -> typ1
  | Variable x, _ -> typ2
  | _, _ -> failwith "Could not unify types"

let unify_monad ?collapse:(collapse=true) (env : 'a FullEnvi.t) (typ1 : t)
  (typ2 : t) : t =
  let f = if collapse then
      (fun d1 d2 ->
        Effect.Descriptor.union @@ match d2 with
        | Some d2 -> [d1; d2]
        | None -> [d1])
    else
      (fun d1 d2 ->
        match d2 with
        | Some d2 -> Effect.Descriptor.union [d1; d2]
        | None -> d1) in
  unify_monad env f typ1 typ2

let union (env : 'a FullEnvi.t) (typs : t list) : t =
  List.fold_left (unify_monad env) Effect.Type.pure typs

let map (f : BoundName.t -> BoundName.t) (typ : t) : t = CommonType.map f typ

let typ_args (typ : t) : Name.Set.t = CommonType.typ_args typ

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

let allocate_implicits_for_monad (implicit_args : (CoqName.t * 'a) list)
  (args : (CoqName.t * 'a) list) (typ : t) : (CoqName.t * 'a) list * t =
  match typ with
  | Monad (d, typ) ->
    if Effect.Descriptor.should_carry d then
      let args' = implicit_args @ args in
      let args' = args' |> List.map (fun (name, _) ->
        snd (CoqName.assoc_names name)) in
      let args_set = Name.Set.of_list args' in
      let rec find_name n =
        let name = "es_in" ^ string_of_int n in
        if Name.Set.mem name args_set then find_name (n+1) else name in
      let name = if Name.Set.mem "es_in" args_set then
          find_name 1
        else "es_in" in
      let d = Effect.Descriptor.set_unioned_arg name d in
      let arg = (CoqName.of_names name name, Variable "list Effect.t") in
      (arg :: implicit_args, Monad (d, typ))
    else
      (implicit_args, Monad (d, typ))
  | _ -> (implicit_args, typ)

let to_json (typ : t) : json = CommonType.to_json typ

let of_json (json : json) : t = CommonType.of_json json

let to_coq (paren : bool) (typ : t) : SmartPrint.t =
  CommonType.to_coq Effect.Descriptor.to_coq paren typ
