open SmartPrint
open Yojson.Basic

include Kerneltypes.Type
type 'a t = 'a Kerneltypes.Type.t'

let rec pp (pp_a : 'a -> SmartPrint.t) (typ : 'a t) : SmartPrint.t =
  let pp = pp pp_a in
  match typ with
  | Variable x -> Name.pp x
  | Arrow (typ1, typ2) -> nest @@ parens (pp typ1 ^^ !^ "->" ^^ pp typ2)
  | Tuple typs -> nest @@ parens (separate (space ^^ !^ "*" ^^ space) (List.map pp typs))
  | Apply (x, typs) ->
    nest (!^ "Type" ^^ nest (parens (
      separate (!^ "," ^^ space) (BoundName.pp x :: List.map pp typs))))
  | Monad (d, typ) -> nest (!^ "Monad" ^^ OCaml.tuple [pp_a d; pp typ])

let rec unify (typ1 : 'a t) (typ2 : 'b t) : 'b t Name.Map.t =
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

let rec unify_monad (f : 'a -> 'a option -> 'a) (typ1 : 'a t) (typ2 : 'a t)
  : 'a t =
  let unify_monad = unify_monad f in
  match typ1, typ2 with
  | _, Variable y -> typ1
  | Variable x, _ -> typ2
  | Arrow (typ1a, typ1b), Arrow (typ2a, typ2b) ->
    Arrow (unify_monad typ1a typ2a, unify_monad typ1b typ2b)
  | Tuple typs1, Tuple typs2 ->
    Tuple (List.map2 unify_monad typs1 typs2)
  | Apply (x1, typs1), Apply (x2, typs2)
    when BoundName.stable_compare x1 x2 = 0 ->
    Apply (x1, List.map2 unify_monad typs1 typs2)
  | Monad (d1, typ1), Monad (d2, typ2) ->
    Monad (f d1 (Some d2), unify_monad typ1 typ2)
  | Monad (d, typ1), typ2 | typ1, Monad (d, typ2) ->
    Monad (f d None, unify_monad typ1 typ2)
  | _, _ -> failwith "Could not unify types"

let rec strip_monads (typ : 'a t) : 'b t =
  match typ with
  | Variable x -> Variable x
  | Arrow (typ1, typ2) -> Arrow (strip_monads typ1, strip_monads typ2)
  | Tuple typs -> Tuple (List.map strip_monads typs)
  | Apply (x, typs) -> Apply (x, List.map strip_monads typs)
  | Monad (x, typ) -> strip_monads typ

let rec map (f : BoundName.t -> BoundName.t) (typ : 'a t) : 'a t =
  match typ with
  | Variable x -> Variable x
  | Arrow (typ_x, typ_y) -> Arrow (map f typ_x, map f typ_y)
  | Tuple typs -> Tuple (List.map (map f) typs)
  | Apply (path, typs) -> Apply (f path, List.map (map f) typs)
  | Monad (x, typ) -> Monad (x, map f typ)

let rec map_vars (f : Name.t -> 'a t) (typ : 'a t) : 'a t =
  match typ with
  | Variable x -> f x
  | Arrow (typ1, typ2) -> Arrow (map_vars f typ1, map_vars f typ2)
  | Tuple typs -> Tuple (List.map (map_vars f) typs)
  | Apply (x, typs) -> Apply (x, List.map (map_vars f) typs)
  | Monad (x, typ) -> Monad (x, map_vars f typ)

let rec has_vars (typ : 'a t) : bool =
  match typ with
  | Variable _ -> true
  | Arrow (typ_x, typ_y) -> has_vars typ_x || has_vars typ_y
  | Tuple typs -> List.exists has_vars typs
  | Apply (_, typs) -> List.exists has_vars typs
  | Monad (x, typ) -> has_vars typ

let rec typ_args (typ : 'a t) : Name.Set.t =
  match typ with
  | Variable x -> Name.Set.singleton x
  | Arrow (typ1, typ2) -> typ_args_of_typs [typ1; typ2]
  | Tuple typs | Apply (_, typs) -> typ_args_of_typs typs
  | Monad (_, typ) -> typ_args typ

and typ_args_of_typs (typs : 'a t list) : Name.Set.t =
  List.fold_left (fun args typ -> Name.Set.union args (typ_args typ))
    Name.Set.empty typs

let rec to_json (a_to_json : 'a -> json) (typ : 'a t) : json =
  let to_json = to_json a_to_json in
  match typ with
  | Variable x -> `List [`String "Variable"; Name.to_json x]
  | Arrow (typ_x, typ_y) ->
    `List [`String "Arrow"; to_json typ_x; to_json typ_y]
  | Tuple typs -> `List (`String "Tuple" :: List.map to_json typs)
  | Apply (path, typs) ->
    `List (`String "Apply" :: BoundName.to_json path :: List.map to_json typs)
  | Monad (descriptor, typ) ->
    `List [`String "Monad"; a_to_json descriptor; to_json typ]

let rec of_json (a_of_json : json -> 'a) (json : json) : 'a t =
  let of_json = of_json a_of_json in
  match json with
  | `List [`String "Variable"; x] -> Variable (Name.of_json x)
  | `List [`String "Arrow"; typ_x; typ_y] ->
    Arrow (of_json typ_x, of_json typ_y)
  | `List (`String "Tuple" :: typs) -> Tuple (List.map of_json typs)
  | `List (`String "Apply" :: path :: typs) ->
    Apply (BoundName.of_json path, List.map of_json typs)
  | `List [`String "Monad"; descriptor; typ] ->
    Monad (a_of_json descriptor, of_json typ)
  | _ -> failwith "Invalid JSON for Type."

(** Pretty-print a type (inside parenthesis if the [paren] flag is set). *)
let rec to_coq (a_to_coq : 'a -> SmartPrint.t) (paren : bool) (typ : 'a t)
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
