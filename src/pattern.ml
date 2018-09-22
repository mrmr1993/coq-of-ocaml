(** Patterns used for the "match". *)
open Typedtree
open SmartPrint

type t =
  | Any
  | Constant of Constant.t
  | Variable of CoqName.t
  | Tuple of t list
  | Constructor of BoundName.t * t list (** A constructor name and a list of pattern in arguments. *)
  | Alias of t * CoqName.t
  | Record of (BoundName.t * t) list (** A list of fields from a record with their expected patterns. *)
  | Or of t * t

let rec pp (p : t) : SmartPrint.t =
  match p with
  | Any -> !^ "Any"
  | Constant c -> Constant.pp c
  | Variable x -> CoqName.pp x
  | Tuple ps -> nest (!^ "Tuple" ^^ OCaml.tuple (List.map pp ps))
  | Constructor (x, ps) ->
    nest (!^ "Constructor" ^^ OCaml.tuple (BoundName.pp x :: List.map pp ps))
  | Alias (p, x) -> nest (!^ "Alias" ^^ OCaml.tuple [pp p; CoqName.pp x])
  | Record fields ->
    nest (!^ "Record" ^^ OCaml.tuple (fields |> List.map (fun (x, p) ->
      nest @@ parens (BoundName.pp x ^-^ !^ "," ^^ pp p))))
  | Or (p1, p2) -> nest (!^ "Or" ^^ OCaml.tuple [pp p1; pp p2])

(** Import an OCaml pattern. *)
let rec of_pattern (new_names : bool) (env : unit FullEnvi.t) (p : pattern) : t =
  let l = Loc.of_location p.pat_loc in
  match p.pat_desc with
  | Tpat_any -> Any
  | Tpat_var (x, _) ->
    let x = Name.of_ident x in
    let x = if new_names then
        let (x, _, _) = FullEnvi.Var.create x () env in x
      else FullEnvi.Var.coq_name x env in
    Variable x
  | Tpat_tuple ps -> Tuple (List.map (of_pattern new_names env) ps)
  | Tpat_construct (x, _, ps) ->
    let x = FullEnvi.Constructor.bound l (PathName.of_loc x) env in
    Constructor (x, List.map (of_pattern new_names env) ps)
  | Tpat_alias (p, x, _) ->
    let x = Name.of_ident x in
    let x = if new_names then
        let (x, _, _) = FullEnvi.Var.create x () env in x
      else FullEnvi.Var.coq_name x env in
    Alias (of_pattern new_names env p, x)
  | Tpat_constant c -> Constant (Constant.of_constant l c)
  | Tpat_record (fields, _) ->
    Record (fields |> List.map (fun (x, _, p) ->
      let x = FullEnvi.Field.bound l (PathName.of_loc x) env in
      (x, of_pattern new_names env p)))
  | Tpat_or (p1, p2, _) ->
    Or (of_pattern new_names env p1, of_pattern new_names env p2)
  | _ -> Error.raise l "Unhandled pattern."

(** Free variables in a pattern. *)
let rec free_variables (p : t) : CoqName.Set.t =
  let aux ps =
    List.fold_left (fun s p -> CoqName.Set.union s (free_variables p))
    CoqName.Set.empty ps in
  match p with
  | Any | Constant _ -> CoqName.Set.empty
  | Variable x -> CoqName.Set.singleton x
  | Tuple ps | Constructor (_, ps) -> aux ps
  | Alias (p, x) ->
    CoqName.Set.union (CoqName.Set.singleton x)
      (free_variables p)
  | Record fields -> aux (List.map snd fields)
  | Or (p1, p2) -> CoqName.Set.inter (free_variables p1) (free_variables p2)

let rec free_typed_variables (field_type : BoundName.t -> Type.t)
  (constructor_types : BoundName.t -> Type.t list) (typ : Type.t) (p : t)
  : Type.t CoqName.Map.t =
  let free_typed_variables = free_typed_variables field_type constructor_types in
  let union = CoqName.Map.union (fun _ a _ -> Some a) in
  let inter = CoqName.Map.merge (fun _ a b ->
    match a, b with
    | Some _, Some _ -> a
    | _, _ -> None) in
  let aux typs ps =
    List.fold_left2 (fun s typ p -> union s (free_typed_variables typ p))
    CoqName.Map.empty typs ps in
  match typ, p with
  | _, Any | _, Constant _ -> CoqName.Map.empty
  | _, Variable x -> CoqName.Map.singleton x typ
  | Type.Tuple typs, Tuple ps -> aux typs ps
  | _, Constructor (c, ps) ->
    aux (constructor_types c) ps
  | _, Alias (p, x) ->
    union (CoqName.Map.singleton x typ) (free_typed_variables typ p)
  | _, Record fields ->
    let typs = List.map (fun (field_name, _) -> field_type field_name) fields in
    aux typs (List.map snd fields)
  | _, Or (p1, p2) ->
    inter (free_typed_variables typ p1) (free_typed_variables typ p2)
  | _, _ -> failwith "Pattern is incompatable with the associated type."

let add_to_env (p : t) (env : unit FullEnvi.t) : unit FullEnvi.t =
  CoqName.Set.fold (fun x env -> FullEnvi.Var.assoc x () env)
    (free_variables p) env

(** Pretty-print a pattern to Coq (inside parenthesis if the [paren] flag is set). *)
let rec to_coq (paren : bool) (p : t) : SmartPrint.t =
  match p with
  | Any -> !^ "_"
  | Constant c -> Constant.to_coq c
  | Variable x -> CoqName.to_coq x
  | Tuple ps ->
    if ps = [] then
      !^ "tt"
    else
      parens @@ nest @@ separate (!^ "," ^^ space) (List.map (to_coq false) ps)
  | Constructor (x, ps) ->
    if ps = [] then
      BoundName.to_coq x
    else
      Pp.parens paren @@ nest @@ separate space (BoundName.to_coq x :: List.map (to_coq true) ps)
  | Alias (p, x) ->
    Pp.parens paren @@ nest (to_coq false p ^^ !^ "as" ^^ CoqName.to_coq x)
  | Record fields ->
    !^ "{|" ^^
    nest_all @@ separate (!^ ";" ^^ space) (fields |> List.map (fun (x, p) ->
      nest (BoundName.to_coq x ^^ !^ ":=" ^^ to_coq false p)))
    ^^ !^ "|}"
  | Or (p1, p2) -> to_coq false p1 ^^ !^ "|" ^^ to_coq false p2
