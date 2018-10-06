open SmartPrint
open Yojson.Basic

module Type = struct
  type typ =
    | Variable of Name.t
    | Arrow of typ * typ
    | Tuple of typ list
    | Apply of BoundName.t * typ list
    | Monad of desc * typ

  and desc = {
    args_arg : Name.t option;
    with_args : typ list;
    no_args : typ list;
  }
end
include Type

module TypeDefinition = struct
  type typ_def =
    | Inductive of CoqName.t * Name.t list * (CoqName.t * typ list) list
    | Record of CoqName.t * Name.t list * (CoqName.t * typ) list
    | Synonym of CoqName.t * Name.t list * typ
    | Abstract of CoqName.t * Name.t list
end

type t = typ

let rec pp (typ : t) : SmartPrint.t =
  match typ with
  | Variable x -> Name.pp x
  | Arrow (typ1, typ2) -> nest @@ parens (pp typ1 ^^ !^ "->" ^^ pp typ2)
  | Tuple typs -> nest @@ parens (separate (space ^^ !^ "*" ^^ space) (List.map pp typs))
  | Apply (x, typs) ->
    nest (!^ "Type" ^^ nest (parens (
      separate (!^ "," ^^ space) (BoundName.pp x :: List.map pp typs))))
  | Monad (d, typ) -> nest (!^ "Monad" ^^ OCaml.tuple [pp_desc d; pp typ])

and pp_desc (d : desc) : SmartPrint.t =
  OCaml.list pp @@ d.with_args @ d.no_args

let compare (typ1 : t) (typ2 : t) : int =
  match typ1, typ2 with
  | Apply (x, typ1), Apply (y, typ2) ->
    let cmp = BoundName.stable_compare x y in
    if cmp == 0 then compare typ1 typ2 else cmp
  | _, _ -> compare typ1 typ2

module Set = Set.Make (struct
  type t = typ
  let compare x y = compare x y
end)

let rec equal (typ1 : t) (typ2 : t) : bool =
  match typ1, typ2 with
  | Variable x, Variable y -> x = y
  | Arrow (typ1a, typ1b), Arrow (typ2a, typ2b) ->
    equal typ1a typ2a && equal typ1b typ2b
  | Tuple typs1, Tuple typs2 -> equal_list typs1 typs2
  | Apply (x, typs1), Apply (y, typs2) ->
    BoundName.stable_compare x y = 0 && equal_list typs1 typs2
  | Monad (d1, typ1), Monad (d2, typ2) -> eq_desc d1 d2 && equal typ1 typ2
  | _, _ -> false

and equal_list (l1 : t list) (l2 : t list) =
  match l1, l2 with
  | [], [] -> true
  | (x :: l1), (y :: l2) -> equal x y && equal_list l1 l2
  | _, _ -> false

and eq_desc (d1 : desc) (d2 : desc) : bool =
  equal_list d1.with_args d2.with_args && equal_list d1.no_args d2.no_args

let rec unify (typ1 : t) (typ2 : t) : t Name.Map.t =
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
  | Apply (x1, typs1), Apply (x2, typs2) ->
    List.fold_left2 (fun var_map typ1 typ2 -> union var_map (unify typ1 typ2))
      Name.Map.empty typs1 typs2
  | _, _ -> failwith "Could not unify types"

let rec unify_monad (f : desc -> desc option -> desc) (typ1 : t) (typ2 : t)
  : t =
  let unify_monad = unify_monad f in
  match typ1, typ2 with
  | Arrow (typ1a, typ1b), Arrow (typ2a, typ2b) ->
    Arrow (unify_monad typ1a typ2a, unify_monad typ1b typ2b)
  | Tuple typs1, Tuple typs2 ->
    Tuple (List.map2 unify_monad typs1 typs2)
  | Apply (x1, typs1), Apply (x2, typs2)
    (*when BoundName.stable_compare x1 x2 = 0*) ->
    Apply (x1, List.map2 unify_monad typs1 typs2)
  | Monad (d1, typ1), Monad (d2, typ2) ->
    Monad (f d1 (Some d2), unify_monad typ1 typ2)
  | Monad (d, typ1), typ2 | typ1, Monad (d, typ2) ->
    Monad (f d None, unify_monad typ1 typ2)
  | _, Variable y -> typ1
  | Variable x, _ -> typ2
  | _, _ -> failwith "Could not unify types"

let rec map (f : BoundName.t -> BoundName.t) (typ : t) : t =
  match typ with
  | Variable x -> Variable x
  | Arrow (typ_x, typ_y) -> Arrow (map f typ_x, map f typ_y)
  | Tuple typs -> Tuple (List.map (map f) typs)
  | Apply (path, typs) -> Apply (f path, List.map (map f) typs)
  | Monad (x, typ) -> Monad (x, map f typ)

let rec map_vars (f : Name.t -> t) (typ : t) : t =
  match typ with
  | Variable x -> f x
  | Arrow (typ1, typ2) -> Arrow (map_vars f typ1, map_vars f typ2)
  | Tuple typs -> Tuple (List.map (map_vars f) typs)
  | Apply (x, typs) -> Apply (x, List.map (map_vars f) typs)
  | Monad (x, typ) -> Monad (x, map_vars f typ)

let rec typ_args (typ : t) : Name.Set.t =
  match typ with
  | Variable x -> Name.Set.singleton x
  | Arrow (typ1, typ2) -> typ_args_of_typs [typ1; typ2]
  | Tuple typs | Apply (_, typs) -> typ_args_of_typs typs
  | Monad (_, typ) -> typ_args typ

and typ_args_of_typs (typs : t list) : Name.Set.t =
  List.fold_left (fun args typ -> Name.Set.union args (typ_args typ))
    Name.Set.empty typs

let rec to_json (typ : t) : json =
  match typ with
  | Variable x -> `List [`String "Variable"; Name.to_json x]
  | Arrow (typ_x, typ_y) ->
    `List [`String "Arrow"; to_json typ_x; to_json typ_y]
  | Tuple typs -> `List (`String "Tuple" :: List.map to_json typs)
  | Apply (path, typs) ->
    `List (`String "Apply" :: BoundName.to_json path :: List.map to_json typs)
  | Monad (descriptor, typ) ->
    `List [`String "Monad"; desc_to_json descriptor; to_json typ]

and desc_to_json (d : desc) : json =
  let unioned = List.map to_json d.with_args in
  let simple = d.no_args |> List.map (fun typ ->
    match typ with
    | Apply (name, []) -> BoundName.to_json name
    | _ -> failwith "Unexpected format of simple effect descriptor.") in
  match unioned, simple with
  | [], [] -> `List []
  | [], _ -> `List simple
  | _, [] -> `List unioned
  | _, _ -> `List [`List unioned; `List simple]

let rec of_json (json : json) : t =
  match json with
  | `List [`String "Variable"; x] -> Variable (Name.of_json x)
  | `List [`String "Arrow"; typ_x; typ_y] ->
    Arrow (of_json typ_x, of_json typ_y)
  | `List (`String "Tuple" :: typs) -> Tuple (List.map of_json typs)
  | `List (`String "Apply" :: path :: typs) ->
    Apply (BoundName.of_json path, List.map of_json typs)
  | `List [`String "Monad"; descriptor; typ] ->
    Monad (desc_of_json descriptor, of_json typ)
  | _ -> failwith "Invalid JSON for Type."

and desc_of_json (json : json) : desc =
  let (unioned, simple) =
  match json with
  | `List [`List unioned; `List simple] -> (unioned, simple)
  | `List ((`List _ :: _) as unioned) -> (unioned, [])
  | `List simple -> ([], simple)
  | _ -> raise (Error.Json "Invalid JSON for Effect.Type") in
  let unioned = List.map of_json unioned in
  let simple = simple |> List.map (fun json ->
    Apply (BoundName.of_json json, [])) in
  { args_arg = None; with_args = unioned; no_args = simple }

(** Pretty-print a type (inside parenthesis if the [paren] flag is set). *)
let rec to_coq (a_to_coq : desc -> SmartPrint.t) (paren : bool) (typ : t)
  : SmartPrint.t =
  let to_coq = to_coq a_to_coq in
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
    Pp.parens paren @@ nest (!^ "M" ^^ a_to_coq d ^^ to_coq true typ)
