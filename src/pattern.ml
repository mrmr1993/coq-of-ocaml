(** Patterns used for the "match". *)
open Typedtree
open SmartPrint

type t =
  | Any of Type.t
  | Constant of Type.t * Constant.t
  | Variable of Type.t * CoqName.t
  | Tuple of Type.t * t list
  | Constructor of Type.t * BoundName.t * t list (** A constructor name and a list of pattern in arguments. *)
  | Alias of Type.t * t * CoqName.t
  | Record of Type.t * (BoundName.t * t) list (** A list of fields from a record with their expected patterns. *)
  | Or of Type.t * t * t

let rec pp (p : t) : SmartPrint.t =
  match p with
  | Any _ -> !^ "Any"
  | Constant (_, c) -> Constant.pp c
  | Variable (_, x) -> CoqName.pp x
  | Tuple (_, ps) -> nest (!^ "Tuple" ^^ OCaml.tuple (List.map pp ps))
  | Constructor (_, x, ps) ->
    nest (!^ "Constructor" ^^ OCaml.tuple (BoundName.pp x :: List.map pp ps))
  | Alias (_, p, x) -> nest (!^ "Alias" ^^ OCaml.tuple [pp p; CoqName.pp x])
  | Record (_, fields) ->
    nest (!^ "Record" ^^ OCaml.tuple (fields |> List.map (fun (x, p) ->
      nest @@ parens (BoundName.pp x ^-^ !^ "," ^^ pp p))))
  | Or (_, p1, p2) -> nest (!^ "Or" ^^ OCaml.tuple [pp p1; pp p2])

let typ (p : t) : Type.t =
  match p with
  | Any typ | Constant (typ, _) | Variable (typ, _) | Tuple (typ, _)
  | Constructor (typ, _, _) | Alias (typ, _, _) | Record (typ, _)
  | Or (typ, _, _) -> typ

(** Import an OCaml pattern. *)
let rec of_pattern  (new_names : bool) (env : unit FullEnvi.t)
  (typ_vars : Name.t Name.Map.t) (p : pattern) : t =
  let l = Loc.of_location p.pat_loc in
  let (typ, typ_vars, _) =
    Type.of_type_expr_new_typ_vars env l typ_vars p.pat_type in
  let of_pattern = of_pattern new_names env typ_vars in
  match p.pat_desc with
  | Tpat_any -> Any typ
  | Tpat_var (x, _) ->
    let x = Name.of_ident x in
    let x = if new_names then
        let (x, _, _) = FullEnvi.Var.create x () env in x
      else FullEnvi.Var.coq_name x env in
    Variable (typ, x)
  | Tpat_tuple ps -> Tuple (typ, List.map of_pattern ps)
  | Tpat_construct (x, _, ps) ->
    let x = FullEnvi.Constructor.bound l (PathName.of_loc x) env in
    Constructor (typ, x, List.map of_pattern ps)
  | Tpat_alias (p, x, _) ->
    let x = Name.of_ident x in
    let x = if new_names then
        let (x, _, _) = FullEnvi.Var.create x () env in x
      else FullEnvi.Var.coq_name x env in
    Alias (typ, of_pattern p, x)
  | Tpat_constant c -> Constant (typ, Constant.of_constant l c)
  | Tpat_record (fields, _) ->
    Record (typ, fields |> List.map (fun (x, _, p) ->
      let x = FullEnvi.Field.bound l (PathName.of_loc x) env in
      (x, of_pattern p)))
  | Tpat_or (p1, p2, _) ->
    Or (typ, of_pattern p1, of_pattern p2)
  | _ -> Error.raise l "Unhandled pattern."

(** Free variables in a pattern. *)
let rec free_variables (p : t) : Type.t CoqName.Map.t =
  let union = CoqName.Map.union (fun _ a _ -> Some a) in
  let inter = CoqName.Map.merge (fun _ a b ->
    match a, b with
    | Some _, Some _ -> a
    | _, _ -> None) in
  let aux ps =
    List.fold_left (fun s p -> union s (free_variables p))
    CoqName.Map.empty ps in
  match p with
  | Any _ | Constant _ -> CoqName.Map.empty
  | Variable (typ, x) -> CoqName.Map.singleton x typ
  | Tuple (_, ps) | Constructor (_, _, ps) -> aux ps
  | Alias (typ, p, x) ->
    union (CoqName.Map.singleton x typ) (free_variables p)
  | Record (_, fields) -> aux (List.map snd fields)
  | Or (_, p1, p2) ->
    inter (free_variables p1) (free_variables p2)

let add_to_env (p : t) (env : unit FullEnvi.t) : unit FullEnvi.t =
  CoqName.Map.fold (fun x typ env -> FullEnvi.Var.assoc x () env)
    (free_variables p) env

let add_to_env_with_effects (p : t) (env : Type.t FullEnvi.t)
  : Type.t FullEnvi.t =
  CoqName.Map.fold FullEnvi.Var.assoc (free_variables p) env

(** Pretty-print a pattern to Coq (inside parenthesis if the [paren] flag is set). *)
let rec to_coq (paren : bool) (p : t) : SmartPrint.t =
  match p with
  | Any _ -> !^ "_"
  | Constant (_, c) -> Constant.to_coq c
  | Variable (_, x) -> CoqName.to_coq x
  | Tuple (_, ps) ->
    if ps = [] then
      !^ "tt"
    else
      parens @@ nest @@ separate (!^ "," ^^ space) (List.map (to_coq false) ps)
  | Constructor (_, x, ps) ->
    if ps = [] then
      BoundName.to_coq x
    else
      Pp.parens paren @@ nest @@ separate space (BoundName.to_coq x :: List.map (to_coq true) ps)
  | Alias (_, p, x) ->
    Pp.parens paren @@ nest (to_coq false p ^^ !^ "as" ^^ CoqName.to_coq x)
  | Record (_, fields) ->
    !^ "{|" ^^
    nest_all @@ separate (!^ ";" ^^ space) (fields |> List.map (fun (x, p) ->
      nest (BoundName.to_coq x ^^ !^ ":=" ^^ to_coq false p)))
    ^^ !^ "|}"
  | Or (_, p1, p2) -> to_coq false p1 ^^ !^ "|" ^^ to_coq false p2
