(** An expression. *)
open Typedtree
open Types
open SmartPrint
open Utils

module Header = struct
  type t = {
    name : CoqName.t;
    typ_vars : Name.t list;
    implicit_args : (CoqName.t * Type.t) list;
    args : (CoqName.t * Type.t) list;
    typ : Type.t }

  let pp (header : t) : SmartPrint.t =
    OCaml.tuple [
      CoqName.pp header.name; OCaml.list Name.pp header.typ_vars;
      OCaml.list (fun (x, typ) -> OCaml.tuple [CoqName.pp x; Type.pp typ])
        (header.implicit_args @ header.args);
      Type.pp header.typ]

  let env_in_header (header : t) (env : 'a FullEnvi.t) (v : 'a)
    : 'a FullEnvi.t =
    (* NOTE: Don't include implicit arguments here: user code should not be
       able to refer to them. *)
    List.fold_left (fun env (x, _) -> FullEnvi.Var.assoc x v env)
      env header.args
end

module Definition = struct
  type 'a t = {
    is_rec : Recursivity.t;
    attribute : Attribute.t;
    cases : (Header.t * 'a) list }

  let pp (pp_a : 'a -> SmartPrint.t) (def : 'a t) : SmartPrint.t =
    OCaml.tuple [Recursivity.pp def.is_rec; Attribute.pp def.attribute;
      def.cases |> OCaml.list (fun (header, e) ->
        OCaml.tuple [Header.pp header; pp_a e])]

  let names (def : 'a t) : CoqName.t list =
    List.map (fun (header, _) -> header.Header.name) def.cases

  let env_after_def (def : 'a t) (env : unit FullEnvi.t) : unit FullEnvi.t =
    List.fold_left (fun env x -> FullEnvi.Var.assoc x () env)
      env (names def)

  let env_in_def (def : 'a t) (env : unit FullEnvi.t) : unit FullEnvi.t =
    if Recursivity.to_bool def.is_rec then
      env_after_def def env
    else
      env

  let map (f : 'a -> 'b) (def : 'a t) : 'b t =
    { def with cases = List.map (fun (header, e) -> (header, f e)) def.cases }
end

(** The simplified OCaml AST we use. We do not use a mutualy recursive type to
    simplify the importation in Coq. *)
type 'a t =
  | Constant of 'a * Constant.t
  | Variable of 'a * BoundName.t
  | Tuple of 'a * 'a t list (** A tuple of expressions. *)
  | Constructor of 'a * BoundName.t * 'a t list
    (** A constructor name and a list of arguments. *)
  | Apply of 'a * 'a t * 'a t list (** An application. *)
  | Function of 'a * CoqName.t * 'a t (** An argument name and a body. *)
  | LetVar of 'a * CoqName.t * 'a t * 'a t
  | LetFun of 'a * 'a t Definition.t * 'a t
  | Match of 'a * 'a t * (Pattern.t * 'a t) list
    (** Match an expression to a list of patterns. *)
  | Record of 'a * (BoundName.t * 'a t option) list * 'a t option
    (** Construct a record giving an expression for each field. *)
  | Field of 'a * 'a t * BoundName.t (** Access to a field of a record. *)
  | IfThenElse of 'a * 'a t * 'a t * 'a t (** The "else" part may be unit. *)
  | For of 'a * CoqName.t * bool * 'a t * 'a t * 'a t (** For loop. *)
  | While of 'a * 'a t * 'a t (** While loop. *)
  | Coerce of 'a * 'a t * Type.t (** Coercion. *)
  | Sequence of 'a * 'a t * 'a t (** A sequence of two expressions. *)
  | Return of 'a * 'a t (** Monadic return. *)
  | Bind of 'a * 'a t * CoqName.t option * 'a t (** Monadic bind. *)
  | Lift of 'a * Effect.Descriptor.t * Effect.Descriptor.t * 'a t
    (** Monadic lift. *)
  | Run of 'a * BoundName.t * Effect.Descriptor.t * 'a t

let rec pp (pp_a : 'a -> SmartPrint.t) (e : 'a t) : SmartPrint.t =
  let pp = pp pp_a in
  match e with
  | Constant (a, c) ->
    nest (!^ "Constant" ^^ OCaml.tuple [pp_a a; Constant.pp c])
  | Variable (a, x) ->
    nest (!^ "Variable" ^^ OCaml.tuple [pp_a a; BoundName.pp x])
  | Tuple (a, es) ->
    nest (!^ "Tuple" ^^ OCaml.tuple (pp_a a :: List.map pp es))
  | Constructor (a, x, es) ->
    nest (!^ "Constructor" ^^
      OCaml.tuple (pp_a a :: BoundName.pp x :: List.map pp es))
  | Apply (a, e_f, e_xs) ->
    nest (!^ "Apply" ^^ OCaml.tuple [pp_a a; pp e_f; OCaml.list pp e_xs])
  | Function (a, x, e) ->
    nest (!^ "Function" ^^ OCaml.tuple [pp_a a; CoqName.pp x; pp e])
  | LetVar (a, x, e1, e2) ->
    nest (!^ "LetVar" ^^
      pp_a a ^^ CoqName.pp x ^^ !^ "=" ^^ pp e1 ^^ !^ "in" ^^ newline ^^
      pp e2)
  | LetFun (a, def, e2) ->
    nest (!^ "LetFun" ^^ pp_a a ^^ newline ^^ indent (Definition.pp pp def) ^^
      !^ "in" ^^ newline ^^ pp e2)
  | Match (a, e, cases) ->
    nest (!^ "Match" ^^ OCaml.tuple [pp_a a; pp e;
      cases |> OCaml.list (fun (p, e) ->
        nest @@ parens (Pattern.pp p ^-^ !^ "," ^^ pp e))])
  | Record (a, fields, base) ->
    nest (!^ "Record" ^^
      OCaml.tuple (pp_a a :: OCaml.option pp base ::
        (fields |> List.map (fun (x, e) ->
          nest @@ parens (BoundName.pp x ^-^ !^ "," ^^ OCaml.option pp e)))))
  | Field (a, e, x) ->
    nest (!^ "Field" ^^ OCaml.tuple [pp_a a; pp e; BoundName.pp x])
  | IfThenElse (a, e1, e2, e3) ->
    nest (!^ "IfThenElse" ^^ OCaml.tuple [pp_a a; pp e1; pp e2; pp e3])
  | For (a, name, down, e1, e2, e) ->
    nest (!^ "For" ^^ OCaml.tuple
      [pp_a a; CoqName.pp name; OCaml.bool down; pp e1; pp e2; pp e])
  | While (a, e1, e2) ->
    nest (!^ "While" ^^ OCaml.tuple [pp_a a; pp e1; pp e2])
  | Coerce (a, e, typ) ->
    nest (!^ "Coerce" ^^ OCaml.tuple [pp_a a; pp e; Type.pp typ])
  | Sequence (a, e1, e2) ->
    nest (!^ "Sequence" ^^ OCaml.tuple [pp_a a; pp e1; pp e2])
  | Return (a, e) -> nest (!^ "Return" ^^ OCaml.tuple [pp_a a; pp e])
  | Bind (a, e1, x, e2) -> nest (!^ "Bind" ^^ OCaml.tuple
    [pp_a a; pp e1; nest (OCaml.option CoqName.pp x); pp e2])
  | Lift (a, d1, d2, e) ->
    nest (!^ "Lift" ^^ OCaml.tuple [
      pp_a a; Effect.Descriptor.pp d1; Effect.Descriptor.pp d2; pp e])
  | Run (a, x, d, e) ->
    nest (!^ "Run" ^^ OCaml.tuple [
      pp_a a; BoundName.pp x; Effect.Descriptor.pp d; pp e])

let annotation (e : 'a t) : 'a =
  match e with
  | Constant (a, _) | Variable (a, _) | Tuple (a, _) | Constructor (a, _, _)
  | Apply (a, _, _) | Function (a, _, _) | LetVar (a, _, _, _)
  | LetFun (a, _, _) | Match (a, _, _) | Record (a, _, _) | Field (a, _, _)
  | IfThenElse (a, _, _, _) | For (a, _, _, _, _, _) | While (a, _, _)
  | Coerce (a, _, _) | Sequence (a, _, _) | Return (a, _) | Bind (a, _, _, _)
  | Lift (a, _, _, _) | Run (a, _, _, _) -> a

let update_annotation (f : 'a -> 'a) (e : 'a t) : 'a t =
  match e with
  | Constant (a, c) -> Constant (f a, c)
  | Variable (a, x) -> Variable (f a, x)
  | Tuple (a, es) -> Tuple (f a, es)
  | Constructor (a, x, es) -> Constructor (f a, x, es)
  | Apply (a, e_f, e_xs) -> Apply (f a, e_f, e_xs)
  | Function (a, x, e) -> Function (f a, x, e)
  | LetVar (a, x, e1, e2) -> LetVar (f a, x, e1, e2)
  | LetFun (a, def, e2) -> LetFun (f a, def, e2)
  | Match (a, e, cases) -> Match (f a, e, cases)
  | Record (a, fields, base) -> Record (f a, fields, base)
  | Field (a, e, x) -> Field (f a, e, x)
  | IfThenElse (a, e1, e2, e3) -> IfThenElse (f a, e1, e2, e3)
  | For (a, name, down, e1, e2, e) -> For (f a, name, down, e1, e2, e)
  | While (a, e1, e2) -> While (f a, e1, e2)
  | Coerce (a, e, typ) -> Coerce (f a, e, typ)
  | Sequence (a, e1, e2) -> Sequence (f a, e1, e2)
  | Return (a, e) -> Return (f a, e)
  | Bind (a, e1, x, e2) -> Bind (f a, e1, x, e2)
  | Lift (a, d1, d2, e) -> Lift (f a, d1, d2, e)
  | Run (a, x, d, e) -> Run (f a, x, d, e)

let rec map (f : 'a -> 'b) (e : 'a t) : 'b t =
  match e with
  | Constant (a, c) -> Constant (f a, c)
  | Variable (a, x) -> Variable (f a, x)
  | Tuple (a, es) -> Tuple (f a, List.map (map f) es)
  | Constructor (a, x, es) -> Constructor (f a, x, List.map (map f) es)
  | Apply (a, e_f, e_xs) -> Apply (f a, map f e_f, List.map (map f) e_xs)
  | Function (a, x, e) -> Function (f a, x, map f e)
  | LetVar (a, x, e1, e2) -> LetVar (f a, x, map f e1, map f e2)
  | LetFun (a, def, e2) -> LetFun (f a, Definition.map (map f) def, map f e2)
  | Match (a, e, cases) ->
    Match (f a, map f e, List.map (fun (p, e) -> (p, map f e)) cases)
  | Record (a, fields, base) ->
    let opt_map = option_map (map f) in
    Record (f a, List.map (fun (x, e) -> (x, opt_map e)) fields, opt_map base)
  | Field (a, e, x) -> Field (f a, map f e, x)
  | IfThenElse (a, e1, e2, e3) ->
    IfThenElse (f a, map f e1, map f e2, map f e3)
  | For (a, name, down, e1, e2, e) ->
    For (f a, name, down, map f e1, map f e2, map f e)
  | While (a, e1, e2) -> While (f a, map f e1, map f e2)
  | Coerce (a, e, typ) -> Coerce (f a, map f e, typ)
  | Sequence (a, e1, e2) -> Sequence (f a, map f e1, map f e2)
  | Return (a, e) -> Return (f a, map f e)
  | Bind (a, e1, x, e2) -> Bind (f a, map f e1, x, map f e2)
  | Lift (a, d1, d2, e) -> Lift (f a, d1, d2, map f e)
  | Run (a, x, d, e) -> Run (f a, x, d, map f e)

(** Take a function expression and make explicit the list of arguments and
    the body. *)
let rec open_function (e : 'a t) : CoqName.t list * 'a t =
  match e with
  | Function (_, x, e) ->
    let (xs, e) = open_function e in
    (x :: xs, e)
  | _ -> ([], e)

(** Import an OCaml expression. *)
let rec of_expression (env : unit FullEnvi.t) (typ_vars : Name.t Name.Map.t)
  (e : expression) : (Loc.t * Type.t) t =
  let l = Loc.of_location e.exp_loc in
  let (typ, typ_vars, _) =
      Type.of_type_expr_new_typ_vars env l typ_vars e.exp_type in
  let a = (l, typ) in
  match e.exp_desc with
  | Texp_ident (path, _, _) ->
    let x = FullEnvi.Var.bound l (PathName.of_path l path) env in
    Variable (a, x)
  | Texp_constant constant -> Constant (a, Constant.of_constant l constant)
  | Texp_let (_, [{ vb_pat = p; vb_expr = e1 }], e2)
    when (match e1.exp_desc with
    | Texp_function _ -> false
    | _ -> true) ->
    let p = Pattern.of_pattern false env typ_vars p in
    let e1 = of_expression env typ_vars e1 in
    (match p with
    | Pattern.Variable (_, x) ->
      let env = FullEnvi.Var.assoc x () env in
      let e2 = of_expression env typ_vars e2 in
      LetVar (a, x, e1, e2)
    | _ ->
      let env = Pattern.add_to_env p env in
      let e2 = of_expression env typ_vars e2 in
      Match (a, e1, [p, e2]))
  | Texp_let (is_rec, cases, e) ->
    let (env, defs) = import_let_fun false env l typ_vars is_rec cases in
    let def = match defs with
    | [def] -> def
    | _ ->
      Error.raise l "Found a destructuring definition where a function was expected." in
    let e = of_expression env typ_vars e in
    LetFun (a, def, e)
  | Texp_function { cases = [{c_lhs = {pat_desc = Tpat_var (x, _)}; c_rhs = e}] }
  | Texp_function { cases = [{c_lhs = { pat_desc = Tpat_alias
    ({ pat_desc = Tpat_any }, x, _)}; c_rhs = e}] } ->
    let x = FullEnvi.Var.coq_name (Name.of_ident x) env in
    let env = FullEnvi.Var.assoc x () env in
    Function (a, x, of_expression env typ_vars e)
  | Texp_function { cases = cases } ->
    let (x, e) = open_cases env typ_vars typ cases in
    Function (a, CoqName.of_names x x, e)
  | Texp_apply (e_f, e_xs) ->
    let l_f = Loc.of_location e_f.exp_loc in
    (match e_f.exp_desc with
    | Texp_ident (path, _, _)
      when PathName.of_path l_f path = PathName.of_name ["Pervasives"] "raise" ->
      (match e_xs with
      | [(_, Some e_x)] ->
        (match e_x.exp_desc with
        | Texp_construct (x, _, es) ->
          let l_exn = Loc.of_location e_x.exp_loc in
          let t_exn = Type.Arrow (
            Type.Apply (FullEnvi.Typ.localize env ["OCaml"] "exn", []),
            Variable "_") in
          let x = PathName.of_loc x in
          let x = FullEnvi.Exception.bound l_exn x env in
          let raise_path = FullEnvi.Exception.find l_exn x env in
          let raise_dsc = FullEnvi.localize (FullEnvi.has_value env) env
            { BoundName.full_path = raise_path; local_path = raise_path } in
          let typs = List.map (fun e_arg ->
            let (t_arg, _, _) = Type.of_type_expr_new_typ_vars env
              (Loc.of_location e_arg.exp_loc) typ_vars e_arg.exp_type in
            t_arg) es in
          let es = List.map (of_expression env typ_vars) es in
          Apply (a, Variable ((l_exn, t_exn), raise_dsc),
            [Tuple ((Loc.Unknown, Type.Tuple typs), es)])
        | _ ->
          Error.raise l "Constructor of an exception expected after a 'raise'.")
      | _ -> Error.raise l "Expected one argument for 'raise'.")
    | _ ->
      let e_f = of_expression env typ_vars e_f in
      let e_xs = List.map (fun (_, e_x) ->
        match e_x with
        | Some e_x -> of_expression env typ_vars e_x
        | None -> Error.raise l "expected an argument") e_xs in
      Apply (a, e_f, e_xs))
  | Texp_match (e, cases, _, _) ->
    let e = of_expression env typ_vars e in
    let (index, rev_cases) = cases |>
      List.fold_left (fun (index, l) {c_lhs = p; c_guard = g; c_rhs = e} ->
        let p = Pattern.of_pattern false env typ_vars p in
        let env = Pattern.add_to_env p env in
        match g with
        | Some g ->
          let index = match index with
            | Some i -> i + 1
            | None -> 1 in
          let g = of_expression env typ_vars g in
          let e = of_expression env typ_vars e in
          (Some index, (p, Some (index, g), e) :: l)
        | None ->
          (index, (p, None, of_expression env typ_vars e) :: l)) (None, []) in
    begin match index with
    | Some _ ->
      let string_t = Type.Apply (FullEnvi.Typ.localize env [] "string", []) in
      let int_t = Type.Apply (FullEnvi.Typ.localize env [] "Z", []) in
      let match_fail = FullEnvi.Var.localize env ["OCaml"]
        "raise_Match_failure" in
      let match_fail_t = Type.Arrow (
        Type.Apply (FullEnvi.Typ.localize env ["OCaml"] "exn", []),
        typ) in
      let (fail_file, fail_line, fail_char) = Loc.to_tuple l in
      let no_match = (Pattern.Any (Type.Tuple [snd @@ annotation e; int_t]),
          Apply ((Loc.Unknown, typ),
          Variable ((Loc.Unknown, match_fail_t), match_fail),
            [Tuple ((Loc.Unknown, Type.Tuple [string_t; int_t; int_t]),
              [Constant ((Loc.Unknown, string_t), Constant.String fail_file);
              Constant ((Loc.Unknown, int_t), Constant.Int fail_line);
              Constant ((Loc.Unknown, int_t), Constant.Int fail_char)])])) in
      let (index_pattern, pattern) = rev_cases
        |> List.fold_left (fun (index_pattern, pattern) (p, g, e) ->
          let pattern_typ = Type.Tuple [Pattern.typ p; int_t] in
          match g with
          | Some (index, g) ->
            let index_pattern = (p,
              IfThenElse ((Loc.Unknown, int_t), g,
                Constant ((Loc.Unknown, int_t), Constant.Int index),
                Constant ((Loc.Unknown, int_t), Constant.Int 0)))
              :: index_pattern in
            let pattern = (Pattern.Tuple (pattern_typ,
                [p; Pattern.Constant (int_t, Constant.Int index)]),
              e) :: pattern in
            (index_pattern, pattern)
          | None ->
            let index_pattern =
              (p, Constant ((Loc.Unknown, int_t), Constant.Int 0))
              :: index_pattern in
            let pattern = (Pattern.Tuple (pattern_typ,
                [p; Pattern.Any int_t]),
              e) :: pattern in
            (index_pattern, pattern)) ([], [no_match]) in
      let (i, x, env) = FullEnvi.Var.fresh "i" () env in
      let tup_t = Type.Tuple [snd (annotation e); int_t] in
      LetVar ((Loc.Unknown, typ), i,
        Match ((Loc.Unknown, int_t), e, index_pattern),
        Match (a,
          Tuple ((Loc.Unknown, tup_t), [e; Variable ((Loc.Unknown, int_t), x)]),
          pattern))
    | None ->
      let cases = rev_cases
        |> List.fold_left (fun l (p, _, e) -> (p, e) :: l) [] in
      Match (a, e, cases)
    end
  | Texp_tuple es -> Tuple (a, List.map (of_expression env typ_vars) es)
  | Texp_construct (x, _, es) ->
    let x = FullEnvi.Constructor.bound l (PathName.of_loc x) env in
    Constructor (a, x, List.map (of_expression env typ_vars) es)
  | Texp_record { fields; extended_expression } ->
    Record (a, Array.to_list fields |> List.map (fun (label, definition) ->
      match definition with
      | Kept _ ->
        begin match label.lbl_res.desc with
        | Tconstr (path, _, _) ->
          let x = FullEnvi.Field.bound l
            { (PathName.of_path l path) with base = label.lbl_name } env in
          (x, None)
        | _ -> Error.raise l "Could not find the type of the record expression."
        end
      | Overridden (x, e) ->
        let loc = Loc.of_location label.lbl_loc in
        let x = FullEnvi.Field.bound loc (PathName.of_loc x) env in
        (x, Some (of_expression env typ_vars e))),
      option_map (of_expression env typ_vars) extended_expression)
  | Texp_field (e, x, _) ->
    let x = FullEnvi.Field.bound l (PathName.of_loc x) env in
    Field (a, of_expression env typ_vars e, x)
  | Texp_ifthenelse (e1, e2, e3) ->
    let e3 = match e3 with
      | None -> Tuple ((Loc.Unknown, Type.Tuple []), [])
      | Some e3 -> of_expression env typ_vars e3 in
    IfThenElse (a, of_expression env typ_vars e1,
      of_expression env typ_vars e2, e3)
  | Texp_sequence (e1, e2) ->
    Sequence (a, of_expression env typ_vars e1, of_expression env typ_vars e2)
  | Texp_try (e1,
    [{c_lhs = {pat_desc = Tpat_construct (x, _, ps)}; c_rhs = e2}]) ->
    let e1 = of_expression env typ_vars e1 in
    let typ1 = snd @@ annotation e1 in
    let x = FullEnvi.Descriptor.bound l (PathName.of_loc x) env in
    let ps = List.map (Pattern.of_pattern false env typ_vars) ps in
    let typ_p = List.map Pattern.typ ps in
    let p = Pattern.Tuple (Type.Tuple typ_p, ps) in
    let exn = Type.Apply (FullEnvi.Typ.localize env ["OCaml"] "exn", []) in
    let typ_sum = Type.Apply (FullEnvi.Typ.localize env [] "sum",
      [typ1; exn]) in
    Match (a, Run ((Loc.Unknown, typ_sum), x, Effect.Descriptor.pure, e1), [
      (let p = Pattern.Constructor (typ_sum,
        FullEnvi.Constructor.localize env [] "inl",
        [Pattern.Variable (typ1, FullEnvi.Var.coq_name "x" env)]) in
      let env = Pattern.add_to_env p env in
      let x = FullEnvi.Var.bound l (PathName.of_name [] "x") env in
      (p, Variable ((Loc.Unknown, typ), x)));
      (let p = Pattern.Constructor (typ_sum,
        FullEnvi.Constructor.localize env [] "inr",
        [p]) in
      let env = Pattern.add_to_env p env in
      let e2 = of_expression env typ_vars e2 in
      (p, e2))])
  | Texp_for (_, p, e1, e2, dir, e) ->
    let down = match dir with
      | Asttypes.Upto -> true
      | Asttypes.Downto -> false in
    let name = env |> FullEnvi.Var.coq_name @@ match p.Parsetree.ppat_desc with
    | Parsetree.Ppat_var x -> x.Asttypes.txt
    | Parsetree.Ppat_any -> "_"
    | _ -> Error.raise l "A variable name instead of a pattern was expected." in
    let env = FullEnvi.Var.assoc name () env in
    let e1 = of_expression env typ_vars e1 in
    let e2 = of_expression env typ_vars e2 in
    let e = of_expression env typ_vars e in
    For (a, name, down, e1, e2, e)
  | Texp_while (e1, e2) ->
    let e1 = of_expression env typ_vars e1 in
    let e2 = of_expression env typ_vars e2 in
    While (a, e1, e2)
  | Texp_setfield _ -> Error.raise l "Set field not handled."
  | Texp_array _ -> Error.raise l "Arrays not handled."
  | Texp_assert e ->
    let assert_function = FullEnvi.Var.localize env ["OCaml"] "assert" in
    let e = of_expression env typ_vars e in
    Apply (a, Variable ((l, Type.Arrow (snd @@ annotation e, typ)),
      assert_function), [e])
  | _ -> Error.raise l "Expression not handled."

(** Generate a variable and a "match" on this variable from a list of
    patterns. *)
and open_cases (env : unit FullEnvi.t) (typ_vars : Name.t Name.Map.t)
  (typ : Type.t) (cases : case list) : Name.t * (Loc.t * Type.t) t =
  let (x, bound_x, env) = FullEnvi.Var.fresh "x" () env in
  let p1 = (List.hd cases).c_lhs in
  let cases = cases |> List.map (fun {c_lhs = p; c_rhs = e} ->
    let p = Pattern.of_pattern false env typ_vars p in
    let env = Pattern.add_to_env p env in
    (p, of_expression env typ_vars e)) in
  let l = Loc.of_location p1.pat_loc in
  let (typ_x, _, _) =
    Type.of_type_expr_new_typ_vars env l typ_vars p1.pat_type in
  let typ = Effect.Type.return_type typ 1 in
  (CoqName.ocaml_name x, Match ((Loc.Unknown, typ),
    Variable ((Loc.Unknown, typ_x), bound_x), cases))

and import_let_fun (new_names : bool) (env : unit FullEnvi.t) (loc : Loc.t)
  (typ_vars : Name.t Name.Map.t) (is_rec : Asttypes.rec_flag)
  (cases : value_binding list)
  : unit FullEnvi.t * (Loc.t * Type.t) t Definition.t list =
  let is_rec = Recursivity.of_rec_flag is_rec in
  let attrs = cases |> List.map (fun { vb_attributes = attrs; vb_expr = e; vb_pat = p } ->
    let { exp_loc = loc } = e in
    let l = Loc.of_location loc in
    let attr = Attribute.of_attributes l attrs in
    (* The attribute @coq_rec is added if the name finishes by "_coq_rec": *)
    match Pattern.of_pattern new_names env typ_vars p with
    | Pattern.Variable (_, x) ->
      let x = CoqName.ocaml_name x in
      if Str.string_match (Str.regexp ".*_coq_rec$") x 0 then
        Attribute.combine l attr Attribute.CoqRec
      else
        attr
    | _ -> attr (* This branch should not be reached. *)) in
  let attr = List.fold_left (Attribute.combine loc) Attribute.None attrs in
  let cases = cases |> (env |> map_with_acc (fun env { vb_pat = p; vb_expr = e } ->
    let loc = Loc.of_location p.pat_loc in
    let p = Pattern.of_pattern new_names env typ_vars p in
    match p with
    | Pattern.Variable (typ, x) ->
      (FullEnvi.Var.assoc x () env, (None, p, [(x, typ)], e, loc))
    | _ ->
      if Recursivity.to_bool is_rec then
        Error.raise loc "Only variables are allowed as a left-hand side of let rec";
      let free_vars = CoqName.Map.bindings @@ Pattern.free_variables p in
      let env = List.fold_left (fun env (x, typ) ->
        FullEnvi.Var.assoc x () env) env free_vars in
      let (x, x_bound, env) = FullEnvi.Var.fresh "temp" () env in
      (env, (Some (x, x_bound), p, free_vars, e, loc)))) in
  let env_with_let = List.fold_left (fun env (bound, _, xs, _, _) ->
      let env = match bound with
        | Some (x, _) -> FullEnvi.Var.assoc x () env
        | None -> env in
      List.fold_left (fun env (x, typ) -> FullEnvi.Var.assoc x () env) env xs)
    env cases in
  let env =
    if Recursivity.to_bool is_rec then
      env_with_let
    else
      env in
  let cases' = cases |> List.map (fun (bound, p, xs, e, loc) ->
    let (e_typ, typ_vars, new_typ_vars) =
      Type.of_type_expr_new_typ_vars env loc typ_vars e.exp_type in
    let e = of_expression env typ_vars e in
    let (args_names, e_body) = open_function e in
    let (args_typs, e_body_typ) =
      Type.open_type e_typ (List.length args_names) in
    match bound with
    | None ->
      let x = match xs with
        | [(x, _)] -> x
        | _ ->
          failwith "No temporary variable allocated for toplevel pattern match." in
      let header = {
        Header.name = x;
        typ_vars = Name.Set.elements new_typ_vars;
        implicit_args = [];
        args = List.combine args_names args_typs;
        typ = e_body_typ } in
      (header, e_body)
    | Some (x, x_bound) ->
      if List.compare_length_with args_names 0 > 0 then
        Error.raise loc "Could not match against a function.";
      match xs with
      | [(y, typ)] ->
        let typ_vars = Type.typ_args typ in
        let new_typ_vars = Name.Set.inter typ_vars new_typ_vars in
        let header = {
          Header.name = y;
          typ_vars = Name.Set.elements new_typ_vars;
          implicit_args = [];
          args = [];
          typ = typ } in
        let y_bound = FullEnvi.Var.bound loc
          (PathName.of_name [] (CoqName.ocaml_name y)) env_with_let in
        (header, Match ((loc, typ), e_body,
          [p, Variable ((loc, typ), y_bound)]))
      | _ ->
        let header = {
          Header.name = x;
          typ_vars = Name.Set.elements new_typ_vars;
          implicit_args = [];
          args = [];
          typ = e_body_typ } in
        (header, e_body)) in
  let def = {
    Definition.is_rec = is_rec;
    attribute = attr;
    cases = cases' } in
  if Recursivity.to_bool is_rec then
    (env_with_let, [def])
  else
    let defs = cases |> List.map (fun (bound, p, xs, e, loc) ->
      match bound, xs with
      | None, _ | _, [_] -> []
      | Some (x, x_bound), _ ->
        let (e_typ, _, new_typ_vars) =
          Type.of_type_expr_new_typ_vars env loc typ_vars e.exp_type in
        let free_vars =
          CoqName.Map.bindings @@ Pattern.free_variables p in
        free_vars |> List.map (fun (y, typ) ->
          let typ_vars = Type.typ_args typ in
          let new_typ_vars = Name.Set.inter typ_vars new_typ_vars in
          let header = {
            Header.name = y;
            typ_vars = Name.Set.elements new_typ_vars;
            implicit_args = [];
            args = [];
            typ = typ } in
          let y_bound = FullEnvi.Var.bound loc
            (PathName.of_name [] (CoqName.ocaml_name y)) env_with_let in
          let case = (header, Match ((Loc.Unknown, typ),
            Variable ((Loc.Unknown, e_typ), x_bound),
            [(p, Variable ((Loc.Unknown, typ), y_bound))])) in
          { Definition.is_rec = is_rec;
            attribute = Attribute.None;
            cases = [case] }))
      |> List.concat in
    (env_with_let, def :: defs)

(** Substitute the name [x] used as a variable (not as a constructor for
    example) in [e] by [e']. *)
let rec substitute (x : Name.t) (e' : 'a t) (e : 'a t) : 'a t =
  match e with
  | Constant _ -> e
  | Variable (_, y) ->
    if PathName.of_name [] x = y.BoundName.local_path then
      e'
    else
      e
  | Tuple (a, es) -> Tuple (a, List.map (substitute x e') es)
  | Constructor (a, y, es) -> Constructor (a, y, List.map (substitute x e') es)
  | Apply (a, e_f, e_xs) ->
    Apply (a, substitute x e' e_f, List.map (substitute x e') e_xs)
  | Function (a, y, e) ->
    if CoqName.ocaml_name y = x then
      Function (a, y, e)
    else
      Function (a, y, substitute x e' e)
  | LetVar (a, y, e1, e2) ->
    let e1 = substitute x e' e1 in
    let e2 = if x = CoqName.ocaml_name y then e2 else substitute x e' e2 in
    LetVar (a, y, e1, e2)
  | LetFun (a, def, e2) ->
    let is_x_a_name = List.exists (fun y -> x = CoqName.ocaml_name y)
      (Definition.names def) in
    let def =
      if (Recursivity.to_bool def.Definition.is_rec && is_x_a_name) then
        def
      else
        { def with Definition.cases =
          def.Definition.cases |> List.map (fun (header, e1) ->
            if List.exists (fun (y, _) -> CoqName.ocaml_name y = x) header.Header.args then
              (header, e1)
            else
              (header, substitute x e' e1)) } in
    let e2 = if is_x_a_name then e2 else substitute x e' e2 in
    LetFun (a, def, e2)
  | Match (a, e, cases) ->
    let e = substitute x e' e in
    let cases = cases |> List.map (fun (p, e) ->
      let ys = Pattern.free_variables p in
      if CoqName.Map.exists (fun y _ -> CoqName.ocaml_name y = x) ys then
        (p, e)
      else
        (p, substitute x e' e)) in
    Match (a, e, cases)
  | Record (a, fields, base) ->
    let opt_sub = option_map (substitute x e') in
    Record (a, List.map (fun (y, e) -> (y, opt_sub e)) fields, opt_sub base)
  | Field (a, e, y) -> Field (a, substitute x e' e, y)
  | IfThenElse (a, e1, e2, e3) ->
    IfThenElse (a, substitute x e' e1, substitute x e' e2, substitute x e' e3)
  | For (a, name, down, e1, e2, e) ->
    For (a, name, down, substitute x e' e1,
      substitute x e' e2,
      substitute x e' e)
  | While (a, e1, e2) -> While (a, substitute x e' e1, substitute x e' e2)
  | Coerce (a, e, typ) -> Coerce (a, substitute x e' e, typ)
  | Sequence (a, e1, e2) ->
    Sequence (a, substitute x e' e1, substitute x e' e2)
  | Run (a, y, n, e) -> Run (a, y, n, substitute x e' e)
  | Return (a, e) -> Return (a, substitute x e' e)
  | Bind (a, e1, y, e2) ->
    let e1 = substitute x e' e1 in
    let e2 =
      match y with
      | None -> substitute x e' e2
      | Some y ->
        if CoqName.ocaml_name y = x then
          e2
        else
          substitute x e' e2 in
    Bind (a, e1, y, e2)
  | Lift (a, d1, d2, e) -> Lift (a, d1, d2, substitute x e' e)

let rec monadise_let_rec (env : unit FullEnvi.t) (e : (Loc.t * Type.t) t)
  : (Loc.t * Type.t) t =
  match e with
  | Constant _ | Variable _ -> e
  | Tuple (a, es) ->
    Tuple (a, List.map (monadise_let_rec env) es)
  | Constructor (a, x, es) ->
    Constructor (a, x, List.map (monadise_let_rec env) es)
  | Apply (a, e_f, e_xs) ->
    Apply (a, monadise_let_rec env e_f, List.map (monadise_let_rec env) e_xs)
  | Function (a, x, e) ->
    let env = FullEnvi.Var.assoc x () env in
    Function (a, x, monadise_let_rec env e)
  | LetVar (a, x, e1, e2) ->
    let e1 = monadise_let_rec env e1 in
    let env = FullEnvi.Var.assoc x () env in
    let e2 = monadise_let_rec env e2 in
    LetVar (a, x, e1, e2)
  | LetFun (a, def, e2) ->
    let (env, defs) = monadise_let_rec_definition env def in
    let e2 = monadise_let_rec env e2 in
    List.fold_right (fun def e2 -> LetFun (a, def, e2)) defs e2
  | Match (a, e, cases) ->
    Match (a, monadise_let_rec env e,
      cases |> List.map (fun (p, e) ->
        let env = Pattern.add_to_env p env in
        (p, monadise_let_rec env e)))
  | Record (a, fields, base) ->
    let opt_mlr = option_map (monadise_let_rec env) in
    Record (a, fields |> List.map (fun (x, e) -> (x, opt_mlr e)), opt_mlr base)
  | Field (a, e, x) -> Field (a, monadise_let_rec env e, x)
  | IfThenElse (a, e1, e2, e3) ->
    IfThenElse (a, monadise_let_rec env e1,
      monadise_let_rec env e2,
      monadise_let_rec env e3)
  | For (a, name, down, e1, e2, e) ->
    For (a, name, down, monadise_let_rec env e1,
      monadise_let_rec env e2,
      monadise_let_rec env e)
  | While (a, e1, e2) ->
    While (a, monadise_let_rec env e1, monadise_let_rec env e2)
  | Coerce (a, e, typ) -> Coerce (a, monadise_let_rec env e, typ)
  | Sequence (a, e1, e2) ->
    Sequence (a, monadise_let_rec env e1,
      monadise_let_rec env e2)
  | Run (a, x, d, e) -> Run (a, x, d, monadise_let_rec env e)
  | Return (a, e) -> monadise_let_rec env e
  | Bind (a, e1, x, e2) ->
    let e1 = monadise_let_rec env e1 in
    let env = match x with
      | None -> env
      | Some x -> FullEnvi.Var.assoc x () env in
    Bind (a, e1, x, monadise_let_rec env e2)
  | Lift (a, d1, d2, e) -> Lift (a, d1, d2, monadise_let_rec env e)

and monadise_let_rec_definition (env : unit FullEnvi.t)
  (def : (Loc.t * Type.t) t Definition.t)
  : unit FullEnvi.t * (Loc.t * Type.t) t Definition.t list =
  if Recursivity.to_bool def.Definition.is_rec &&
    def.Definition.attribute <> Attribute.CoqRec then
    let var (x : Name.t) (typ : Type.t) env : (Loc.t * Type.t) t =
      Variable ((Loc.Unknown, typ),
        FullEnvi.Var.bound Loc.Unknown (PathName.of_name [] x) env) in
    let env_in_def = Definition.env_in_def def env in
    (* Add the suffix "_rec" to the names. *)
    let def' = { def with Definition.cases =
      def.Definition.cases |> List.map (fun (header, e) ->
        let (name_rec, _, _) = FullEnvi.Var.fresh
          (CoqName.ocaml_name header.Header.name ^ "_rec") () env_in_def in
        ({ header with Header.name = name_rec }, e)) } in
    let env_after_def' = Definition.env_in_def def' env in
    let nat_type = Type.Apply (FullEnvi.Typ.localize env_after_def' [] "nat",
      []) in
    (* Add the argument "counter" and monadise the bodies. *)
    let def' = { def' with Definition.cases =
      def'.Definition.cases |> List.map (fun (header, e) ->
        let name_rec = header.Header.name in
        let (counter, _, _) =
          FullEnvi.Var.fresh "counter" () env_after_def' in
        let args_rec = (counter, nat_type)
          :: header.Header.args in
        let header_rec =
          { header with Header.name = name_rec; args = args_rec } in
        let env_in_name_rec =
          Header.env_in_header header_rec env_after_def' () in
        let e_name_rec = monadise_let_rec env_in_name_rec e in
        (header_rec, e_name_rec)) } in
    (* Do the substitutions. *)
    let def' = { def' with Definition.cases = List.map2 (fun name (header, e) ->
      let (counter, counter_typ) = List.hd header.Header.args in
      let env = Header.env_in_header header env_after_def' () in
      let rec_typ = List.fold_right (fun (_, arg_typ) typ ->
          Type.Arrow (arg_typ, typ))
        (List.tl header.Header.args) header.Header.typ in
      let e_name_rec =
        List.fold_left2 (fun e_name_rec name (header, e) ->
          substitute (snd (CoqName.assoc_names name))
            (Apply ((Loc.Unknown, rec_typ),
              var (CoqName.ocaml_name header.Header.name)
                (Arrow (counter_typ, rec_typ)) env,
              [var (CoqName.ocaml_name counter) counter_typ env])) e_name_rec)
          e (Definition.names def) def'.Definition.cases in
      let nt_type = snd (annotation e_name_rec) in
      let e_name_rec = Match ((Loc.Unknown, nt_type),
        var (CoqName.ocaml_name counter) counter_typ env, [
        (Pattern.Constructor
            (nat_type, FullEnvi.Constructor.localize env [] "O", []),
          Apply ((Loc.Unknown, nt_type), var "not_terminated"
              (Type.Arrow (Type.Tuple [], nt_type)) env,
            [Tuple ((Loc.Unknown, Type.Tuple []), [])]));
        (Pattern.Constructor
            (nat_type, FullEnvi.Constructor.localize env [] "S",
              [Pattern.Variable (nat_type, counter)]),
          e_name_rec)]) in
      (header, e_name_rec))
      (Definition.names def) def'.Definition.cases } in
    (* Add the definitions without the "_rec" suffix. *)
    let defs = List.map2 (fun name_rec (header, rec_e) ->
      let env = Header.env_in_header header env_after_def' () in
      let rec_typ = List.fold_right (fun (_, arg_typ) typ ->
          Type.Arrow (arg_typ, typ))
        header.Header.args header.Header.typ in
      let e = Apply ((Loc.Unknown, snd (annotation rec_e)),
        var (CoqName.ocaml_name name_rec) (Type.Arrow (nat_type, rec_typ)) env,
        Apply ((Loc.Unknown, nat_type),
          var "read_counter" (Type.Arrow (Type.Tuple [], nat_type)) env,
          [Tuple ((Loc.Unknown, Type.Tuple []), [])])
        :: List.map (fun (x, typ) -> var (CoqName.ocaml_name x) typ env)
          header.Header.args) in
      { Definition.is_rec = Recursivity.New false;
        attribute = Attribute.None;
        cases = [header, e] })
      (Definition.names def') def.Definition.cases in
    let env =
      List.fold_left (fun env def -> Definition.env_after_def def env)
        env defs in
    (env, def' :: defs)
  else
    let def = { def with
      Definition.cases = def.Definition.cases |> List.map (fun (header, e) ->
        (header, monadise_let_rec (Header.env_in_header header env ()) e)) } in
    let env = Definition.env_after_def def env in
    (env, [def])

let rec effects (env : Type.t FullEnvi.t) (e : (Loc.t * Type.t) t)
  : (Loc.t * Type.t) t =
  let compound (es : (Loc.t * Type.t) t list)
  : Effect.Descriptor.t * (Loc.t * Type.t) t list * Type.t list =
    let es = List.map (effects env) es in
    let effects = List.map (fun e -> Effect.split @@ snd @@ annotation e) es in
    let descriptor = Effect.Descriptor.union @@ List.map fst effects in
    let effects = List.map snd effects in
    (descriptor, es, effects) in
  match e with
  | Constant ((l, typ), c) -> Constant ((l, typ), c)
  | Variable ((l, typ), x) ->
    begin try
      let typ' = FullEnvi.Var.find l x env in
      let vars_map = Type.unify typ' typ in
      let typ' = Effect.map_type_vars vars_map typ' in
      let typ = Effect.Type.unify ~collapse:false typ typ' in
      Variable ((l, typ), x)
    with Not_found ->
      let message = BoundName.pp x ^^ !^ "not found: supposed to be pure." in
      Error.warn l (SmartPrint.to_string 80 2 message);
      Variable ((l, typ), x)
    end
  | Tuple ((l, typ), es) ->
    let (d, es, typs) = compound es in
    let typ = Effect.Type.unify typ @@ Effect.join d @@ Type.Tuple typs in
    Tuple ((l, typ), es)
  | Constructor ((l, typ), x, es) ->
    let (d, es, typs) = compound es in
    let typ = Effect.join d typ in
    if not (List.for_all Effect.Type.is_pure typs) then
      Error.warn l "Constructors cannot have functional effects; effect ignored.";
    Constructor ((l, typ), x, es)
  | Apply ((l, typ), e_f, e_xs) ->
    let e_f = effects env e_f in
    let (_, effect_e_f) = Effect.split @@ snd (annotation e_f) in
    let e_xs = List.map (effects env) e_xs in
    let arguments_are_pure = e_xs |> List.for_all (fun e_x ->
      Effect.Type.is_pure @@ snd @@ Effect.split @@ snd @@ annotation e_x) in
    if arguments_are_pure then
      let e_xss = Effect.Type.split_calls effect_e_f e_xs in
      List.fold_left (fun e (e_xs, d) ->
        let (d_e, typ_e) = Effect.split @@ snd (annotation e) in
        let descriptor = Effect.Descriptor.union (d_e ::
          Effect.Type.return_descriptor typ_e (List.length e_xs) ::
          List.map (fun e_x ->
            fst @@ Effect.split @@ snd @@ annotation e_x) e_xs) in
        let typ = Effect.Type.return_type typ_e (List.length e_xs) in
        let typ = Effect.join descriptor typ in
        Apply ((l, typ), e, e_xs))
        e_f e_xss
    else
      Error.raise l "Function arguments cannot have functional effects."
  | Function ((l, typ), x, e) ->
    let env = FullEnvi.Var.assoc x Effect.pure env in
    let e = effects env e in
    let typ = Effect.Type.unify typ @@
      Type.Arrow (Variable "_", snd (annotation e)) in
    Function ((l, typ), x, e)
  | LetVar ((l, typ), x, e1, e2) ->
    let e1 = effects env e1 in
    let (d1, typ1) = Effect.split @@ snd (annotation e1) in
    let env = FullEnvi.Var.assoc x typ1 env in
    let e2 = effects env e2 in
    let (d2, typ2) = Effect.split @@ snd (annotation e2) in
    let descriptor = Effect.Descriptor.union [d1; d2] in
    let effect = Effect.Type.unify typ @@ Effect.join descriptor typ2 in
    LetVar ((l, effect), x, e1, e2)
  | LetFun ((l, typ), def, e2) ->
    let def = effects_of_def env def in
    let env = env_after_def_with_effects env def in
    let e2 = effects env e2 in
    let effect2 = snd (annotation e2) in
    LetFun ((l, effect2), def, e2)
  | Match ((l, typ), e, cases) ->
    let e = effects env e in
    let (d_e, typ_e) = Effect.split @@ snd (annotation e) in
    if Effect.Type.is_pure typ_e then
      let cases = cases |> List.map (fun (p, e') ->
        let p = Pattern.unify env l (snd @@ annotation e) p in
        let env = Pattern.add_to_env_with_effects p env in
        (p, effects env e')) in
      let (d, typ_cases) = Effect.split @@
        Effect.union (List.map (fun (_, e) -> snd (annotation e)) cases) in
      let descriptor = Effect.Descriptor.union [d_e; d] in
      let typ = Effect.Type.unify typ @@ Effect.join descriptor typ_cases in
      Match ((l, typ), e, cases)
    else
      Error.raise l "Cannot match a value with functional effects."
  | Record ((l, typ), fields, base) ->
    let (base, (d, es, typs)) =
      let expressions = option_filter @@ List.map snd fields in
      match base with
      | Some base ->
        begin match compound (base :: expressions) with
        | (d, base :: es, typs) -> (Some base, (d, es, typs))
        | _ -> failwith "Wrong answer from 'compound'." end
      | None -> (None, compound expressions) in
    if not (List.for_all Effect.Type.is_pure typs) then
      Error.warn l "Record field values cannot have functional effects; effect ignored.";
    let fields = mix_map2 (fun (_, x) -> is_some x)
      (fun (x, _) -> (x, None)) (fun (x, _) e -> (x, Some e)) fields es in
    let typ = Effect.join d typ in
    Record ((l, typ), fields, base)
  | Field ((l, typ), e, x) ->
    let e = effects env e in
    let (d, typ') = Effect.split @@ snd @@ annotation e in
    if not (Effect.Type.is_pure typ') then
      Error.warn l "Field cannot be taken of a value with functional effects; effect ignored.";
    let typ = Effect.join d typ in
    Field ((l, typ), e, x)
  | IfThenElse ((l, typ), e1, e2, e3) ->
    let e1 = effects env e1 in
    let (d1, typ1) = Effect.split @@ snd @@ annotation e1 in
    if not (Effect.Type.is_pure typ1) then
      Error.warn l "If cannot be taken of a value with functional effects; effect ignored.";
    let (d, e2, e3, typ2, typ3) = match compound [e2; e3] with
    | (d, [e2; e3], [typ2; typ3]) -> (d, e2, e3, typ2, typ3)
    | _ -> failwith "Wrong answer from 'compound'." in
    let d = Effect.Descriptor.union [d1; d] in
    let typ = Effect.Type.unify typ @@ Effect.join d @@
      Effect.Type.unify typ2 typ3 in
    IfThenElse ((l, typ), e1, e2, e3)
  | For ((l, typ), name, down, e1, e2, e) ->
    let typ_e = snd @@ annotation e in
    let typ_e' = Type.map_vars (fun _ -> Type.Tuple []) typ_e in
    (* Give Coq a concrete type if it can't infer one. *)
    let e = if typ_e = typ_e' then e else
      Coerce ((Loc.Unknown, typ_e'), e, typ_e') in
    let (d, e, e1, e2) = match compound [e; e1; e2] with
      | (d, [e; e1; e2], _) -> (d, e, e1, e2)
      | _ -> failwith "Wrong answer from 'compound'." in
    (* We don't use the actual type of [e] here, since OCaml ignores it, and
       thus it won't necessarily unify with [unit]. We choose not to insert an
       [ignore] call, since it can bloat the generated code significantly for
       exactly the same effect. *)
    let typ = Effect.join d typ in
    For ((l, typ), name, down, e1, e2, e)
  | While ((l, typ), e1, e2) ->
    let typ2 = snd @@ annotation e2 in
    let typ2' = Type.map_vars (fun _ -> Type.Tuple []) typ2 in
    (* Give Coq a concrete type if it can't infer one. *)
    let e2 = if typ2 = typ2' then e2 else
      Coerce ((Loc.Unknown, typ2'), e2, typ2') in
    let (d, e1, e2) = match compound [e1; e2] with
      | (d, [e1; e2], _) -> (d, e1, e2)
      | _ -> failwith "Wrong answer from 'compound'." in
    let counter = FullEnvi.Descriptor.localize env [] "Counter" in
    let nonterm = FullEnvi.Descriptor.localize env [] "NonTermination" in
    let loop_d = Effect.Descriptor.union [
        Effect.Descriptor.singleton counter [];
        Effect.Descriptor.singleton nonterm [];
      ] in
    (* We don't use the actual type of [e2] here, since OCaml ignores it, and
       thus it won't necessarily unify with [unit]. We choose not to insert an
       [ignore] call, since it can bloat the generated code significantly for
       exactly the same effect. *)
    let typ = Effect.join (Effect.Descriptor.union [loop_d; d]) typ in
    While ((l, typ), e1, e2)
  | Coerce ((l, _), e, typ) ->
    let e = effects env e in
    Coerce ((l, snd (annotation e)), e, typ)
  | Sequence ((l, typ), e1, e2) ->
    let (d, e1, e2, typ2) = match compound [e1; e2] with
      | (d, [e1; e2], [_; typ2]) -> (d, e1, e2, typ2)
      | _ -> failwith "Wrong answer from 'compound'." in
    let typ = Effect.Type.unify typ @@ Effect.join d typ2 in
    Sequence ((l, typ), e1, e2)
  | Run ((l, typ), x, d, e) ->
    let e = effects env e in
    let (d_e, typ_e) = Effect.split @@ snd @@ annotation e in
    let exn = Type.Apply (FullEnvi.Typ.localize env ["OCaml"] "exn", []) in
    let typ = Effect.Type.unify typ @@
      Effect.join (Effect.Descriptor.remove x d_e) @@
      Type.Apply (FullEnvi.Typ.localize env [] "sum", [typ_e; exn]) in
    Run ((l, typ), x, d, e)
  | Return _ | Bind _ | Lift _ ->
    Error.raise Loc.Unknown
      "Cannot compute effects on an explicit return, bind or lift."

and env_after_def_with_effects (env : Type.t FullEnvi.t)
  (def : (Loc.t * Type.t) t Definition.t) : Type.t FullEnvi.t =
  List.fold_left (fun env (header, e) ->
    let effect = snd (annotation e) in
    let effect_typ = Effect.function_typ header.Header.args effect in
    FullEnvi.Var.assoc header.Header.name effect_typ env)
    env def.Definition.cases

and effects_of_def_step (env : Type.t FullEnvi.t)
  (def : (Loc.t * Type.t) t Definition.t) : (Loc.t * Type.t) t Definition.t =
  { def with Definition.cases =
    def.Definition.cases |> List.map (fun (header, e) ->
      let env = Header.env_in_header header env Effect.pure in
      let e = effects env e in
      let typ = Effect.Type.unify header.Header.typ @@ snd @@ annotation e in
      ({ header with Header.typ = typ }, e)) }

and effects_of_def (env : Type.t FullEnvi.t)
  (def : (Loc.t * Type.t) t Definition.t) : (Loc.t * Type.t) t Definition.t =
  let rec fix_effect (def' : (Loc.t * Type.t) t Definition.t) =
    let env =
      if Recursivity.to_bool def.Definition.is_rec then
        env_after_def_with_effects env def'
      else
        env in
    let def'' = effects_of_def_step env def in
    if def' = def'' then
      def'
    else
      fix_effect def'' in
  let env =
    if Recursivity.to_bool def.Definition.is_rec then
      List.fold_left (fun env (header, _) ->
        FullEnvi.Var.assoc header.Header.name Effect.pure env)
        env def.Definition.cases
    else
      env in
  fix_effect (effects_of_def_step env def)

let rec monadise (env : unit FullEnvi.t) (e : (Loc.t * Type.t) t) : Loc.t t =
  let descriptor e = fst @@ Effect.split @@ snd @@ annotation e in
  let lift d1 d2 e =
    if Effect.Descriptor.eq d1 d2 then
      e
    else if Effect.Descriptor.is_pure d1 then
      Return (Loc.Unknown, e)
    else
      Lift (Loc.Unknown, d1, d2, e) in
  (** [d1] is the descriptor of [e1], [d2] of [e2]. *)
  let bind d1 d2 d e1 x e2 =
    if Effect.Descriptor.is_pure d1 then
      match x with
      | Some x -> LetVar (Loc.Unknown, x, e1, e2)
      | None -> e2
    else
      Bind (Loc.Unknown, lift d1 d e1, x, lift d2 d e2) in
  (** [k es'] is supposed to raise the effect [d]. *)
  let rec monadise_list env es d es' k =
    match es with
    | [] -> k (List.rev es')
    | e :: es ->
      let d_e = descriptor e in
      if Effect.Descriptor.is_pure d_e then
        monadise_list env es d (map fst e :: es') k
      else
        let e' = monadise env e in
        let (x, bound_x, env) = FullEnvi.Var.fresh "x" () env in
        bind d_e d d e' (Some x) (monadise_list env es d
          (Variable (Loc.Unknown, bound_x) :: es') k) in
  let d = descriptor e in
  match e with
  | Constant ((l, _), c) -> Constant (l, c)
  | Variable ((l, _), x) -> Variable (l, x)
  | Tuple ((l, _), es) ->
    monadise_list env es d [] (fun es' ->
      lift Effect.Descriptor.pure d (Tuple (l, es')))
  | Constructor ((l, _), x, es) ->
    monadise_list env es d [] (fun es' ->
      lift Effect.Descriptor.pure d (Constructor (l, x, es')))
  | Apply ((l, _), e_f, e_xs) ->
    let effect_f = snd @@ Effect.split @@ snd @@ annotation e_f in
    monadise_list env (e_f :: e_xs) d [] (fun es' ->
      match es' with
      | e_f :: e_xs ->
        let return_descriptor =
          Effect.Type.return_single_descriptor effect_f (List.length e_xs) in
        lift return_descriptor d (Apply (l, e_f, e_xs))
      | _ -> failwith "Wrong answer from 'monadise_list'.")
  | Function ((l, _), x, e) ->
    let env = FullEnvi.Var.assoc x () env in
    Function (l, x, monadise env e)
  | LetVar ((l, _), x, e1, e2) -> (* TODO: use l *)
    let (d1, d2) = (descriptor e1, descriptor e2) in
    let e1 = monadise env e1 in
    let env = FullEnvi.Var.assoc x () env in
    let e2 = monadise env e2 in
    bind d1 d2 d e1 (Some x) e2
  | LetFun ((l, _), def, e2) ->
    let env_in_def = Definition.env_in_def def env in
    let def = { def with
      Definition.cases = def.Definition.cases |> List.map (fun (header, e) ->
      let env = Header.env_in_header header env_in_def () in
      let e = monadise env e in
      (header, e)) } in
    let env = Definition.env_after_def def env in
    let e2 = monadise env e2 in
    LetFun (l, def, e2)
  | Match ((l, _), e, cases) ->
    monadise_list env [e] d [] (fun es' ->
      match es' with
      | [e] ->
        let cases = cases |> List.map (fun (p, e)->
          let env = Pattern.add_to_env p env in
          (p, lift (descriptor e) d (monadise env e))) in
        Match (l, e, cases)
      | _ -> failwith "Wrong answer from 'monadise_list'.")
  | Record ((l, _), fields, base) ->
    let expressions = option_filter @@ List.map snd fields in
    let expressions = match base with
      | Some base -> base :: expressions
      | None -> expressions in
    monadise_list env expressions d [] (fun es' ->
      let (base, es', get_base_field) = match base with
        | Some _ -> begin match es' with
          | base :: es' ->
            (Some base, es', fun x -> Some (Field (Loc.Unknown, base, x)))
          | _ -> failwith "Wrong answer from 'monadise_list'." end
        | None -> (None, es', fun _ -> None) in
      let fields = mix_map2 (fun (_, x) -> is_some x)
        (fun (x, _) -> (x, get_base_field x))
        (fun (x, _) e -> (x, Some e)) fields es' in
      lift Effect.Descriptor.pure d (Record (l, fields, base)))
  | Field ((l, _), e, x) ->
    monadise_list env [e] d [] (fun es' ->
      match es' with
      | [e] -> lift Effect.Descriptor.pure d (Field (l, e, x))
      | _ -> failwith "Wrong answer from 'monadise_list'.")
  | IfThenElse ((l, _), e1, e2, e3) ->
    let (d2, d3) = (descriptor e2, descriptor e3) in
    monadise_list env [e1] d [] (fun es' ->
      match es' with
      | [e1] ->
        let e2 = lift d2 d (monadise env e2) in
        let e3 = lift d3 d (monadise env e3) in
        IfThenElse (l, e1, e2, e3)
      | _ -> failwith "Wrong answer from 'monadise_list'.")
  | For ((l, _), name, down, e1, e2, e) ->
    monadise_list env [e1; e2] d [] (fun es' ->
      match es' with
      | [e1; e2] ->
        let e = lift (descriptor e) d (monadise env e) in
        let for_name = if down then "for_to" else "for_downto" in
        let bound_for = FullEnvi.Var.localize env ["OCaml"; "Basics"] for_name in
        Apply (l, Variable (Loc.Unknown, bound_for),
          [e1; e2; Function (Loc.Unknown, name, e)])
      | _ -> failwith "Wrong answer from 'monadise_list'.")
  | While ((l, d), e1, e2) ->
    let counter = FullEnvi.Descriptor.localize env [] "Counter" in
    let nonterm = FullEnvi.Descriptor.localize env [] "NonTermination" in
    let read_counter = FullEnvi.Var.localize env [] "read_counter" in
    let not_terminated = FullEnvi.Var.localize env [] "not_terminated" in
    let tt = FullEnvi.Constructor.localize env [] "tt" in
    let nat = Type.Apply (FullEnvi.Typ.localize env [] "nat", []) in
    let o = FullEnvi.Constructor.localize env [] "O" in
    let s = FullEnvi.Constructor.localize env [] "S" in
    let counter_d = Effect.Descriptor.singleton counter [] in
    let nonterm_d = Effect.Descriptor.singleton nonterm [] in
    let (while_name, while_bound, env) = FullEnvi.Var.fresh "while" () env in
    let (counter_name, counter_bound, env) =
      FullEnvi.Var.fresh "counter" () env in
    let (check_name, check_bound, env) =
      FullEnvi.Var.fresh "check" () env in
    let d = fst @@ Effect.split d in
    let d1 = descriptor e1 in
    let d2 = descriptor e2 in
    let while_d = Effect.Descriptor.union [nonterm_d; d1; d2] in
    LetFun (l, {
        Definition.is_rec = Recursivity.New true;
        attribute = Attribute.None;
        cases = [{
            Header.name = while_name;
            typ_vars = [];
            implicit_args = [];
            args = [(counter_name, nat)];
            typ = Monad (while_d, Type.Tuple [])
          },
          Match (Loc.Unknown, Variable (Loc.Unknown, counter_bound), [
            (Pattern.Constructor (nat, o, []),
            lift nonterm_d while_d
              (Apply (Loc.Unknown, Variable (Loc.Unknown, not_terminated),
                [Constructor (Loc.Unknown, tt, [])])));
            (Pattern.Constructor (nat, s,
              [Pattern.Variable (nat, counter_name)]),
            bind d1 while_d while_d (monadise env e1) (Some check_name)
              (IfThenElse (Loc.Unknown, Variable (Loc.Unknown, check_bound),
                bind d2 while_d while_d (monadise env e2) None
                  (Apply (Loc.Unknown, Variable (Loc.Unknown, while_bound),
                    [Variable (Loc.Unknown, counter_bound)])),
                (Return (Loc.Unknown, Constructor (Loc.Unknown, tt, [])))
            )))
          ])]},
      bind counter_d while_d d
        (Apply (Loc.Unknown, Variable (Loc.Unknown, read_counter),
          [Constructor (Loc.Unknown, tt, [])]))
        (Some counter_name)
        (Apply (Loc.Unknown, Variable (Loc.Unknown, while_bound),
          [Variable (Loc.Unknown, counter_bound)]))
    )
  | Coerce ((l, d), e, typ) ->
    Coerce (l, monadise env e, Effect.Type.unify d typ)
  | Sequence ((l, _), e1, e2) -> (* TODO: use l *)
    let (d1, d2) = (descriptor e1, descriptor e2) in
    let e1 = monadise env e1 in
    let e2 = monadise env e2 in
    bind d1 d2 d e1 None e2
  | Run ((l, _), x, _, e) ->
    Run (l, x, descriptor e, monadise env e)
  | Return _ | Bind _ | Lift _ ->
    failwith "Unexpected arguments for 'monadise'."

(** Pretty-print an expression to Coq (inside parenthesis if the [paren] flag is
    set). *)
let rec to_coq (paren : bool) (e : 'a t) : SmartPrint.t =
  match e with
  | Constant (_, c) -> Constant.to_coq c
  | Variable (_, x) -> BoundName.to_coq x
  | Tuple (_, es) ->
    if es = [] then
      !^ "tt"
    else
      parens @@ nest @@ separate (!^ "," ^^ space) (List.map (to_coq true) es)
  | Constructor (_, x, es) ->
    if es = [] then
      BoundName.to_coq x
    else
      Pp.parens paren @@ nest @@ separate space
        (BoundName.to_coq x :: List.map (to_coq true) es)
  | Apply (_, e_f, e_xs) ->
    Pp.parens paren @@ nest @@ (separate space (List.map (to_coq true) (e_f :: e_xs)))
  | Function (_, x, e) ->
    Pp.parens paren @@ nest (!^ "fun" ^^ CoqName.to_coq x ^^ !^ "=>" ^^ to_coq false e)
  | LetVar (_, x, e1, e2) ->
    Pp.parens paren @@ nest (
      !^ "let" ^^ CoqName.to_coq x ^-^ !^ " :=" ^^ to_coq false e1 ^^ !^ "in" ^^ newline ^^ to_coq false e2)
  | LetFun (_, def, e) ->
    let firt_case = ref true in (* TODO: say that 'let rec and' is not supported (yet?) inside expressions. *)
    Pp.parens paren @@ nest (separate newline
      (def.Definition.cases |> List.map (fun (header, e) ->
        (if !firt_case then (
          firt_case := false;
          !^ "let" ^^
          (if Recursivity.to_bool def.Definition.is_rec then !^ "fix" else empty)
        ) else
          !^ "with") ^^
        CoqName.to_coq header.Header.name ^^
        (if header.Header.typ_vars = []
        then empty
        else braces @@ group (
          separate space (List.map Name.to_coq header.Header.typ_vars) ^^
          !^ ":" ^^ !^ "Type")) ^^
        group (separate space (header.Header.implicit_args
          |> List.map (fun (x, x_typ) ->
            braces (CoqName.to_coq x ^^ !^ ":" ^^ Type.to_coq false x_typ)))) ^^
        group (separate space (header.Header.args |> List.map (fun (x, x_typ) ->
          parens (CoqName.to_coq x ^^ !^ ":" ^^ Type.to_coq false x_typ)))) ^^
        !^ ": " ^-^ Type.to_coq false header.Header.typ ^-^
        !^ " :=" ^^ newline ^^
        indent (to_coq false e))) ^^ !^ "in" ^^ newline ^^ to_coq false e)
  | Match (_, e, cases) ->
    nest (
      !^ "match" ^^ to_coq false e ^^ !^ "with" ^^ newline ^^
      separate space (cases |> List.map (fun (p, e) ->
        nest (!^ "|" ^^ Pattern.to_coq false p ^^ !^ "=>" ^^ to_coq false e ^^ newline))) ^^
      !^ "end")
  | Record (_, fields, _) ->
    nest (!^ "{|" ^^ separate (!^ ";" ^^ space)
      (fields |> filter_map (fun (x, e) -> e |> option_map (fun e ->
        nest (BoundName.to_coq x ^-^ !^ " :=" ^^ to_coq false e)))) ^^ !^ "|}")
  | Field (_, e, x) -> Pp.parens paren @@ nest (BoundName.to_coq x ^^ to_coq true e)
  | IfThenElse (_, e1, e2, e3) ->
    Pp.parens paren @@ nest (
      !^ "if" ^^ to_coq false e1 ^^ !^ "then" ^^ newline ^^
      indent (to_coq false e2) ^^ newline ^^
      !^ "else" ^^ newline ^^
      indent (to_coq false e3))
  | For _ -> failwith "Cannot output for statement: should have already been converted."
  | While _ -> failwith "Cannot output while statement: should have already been converted."
  | Coerce (_, e, typ) ->
    Pp.parens paren @@ nest @@ to_coq true e ^^ !^ ":" ^^ Type.to_coq false typ
  | Sequence (_, e1, e2) ->
    nest (to_coq true e1 ^-^ !^ ";" ^^ newline ^^ to_coq false e2)
  | Run (_, x, d, e) ->
    let n = Effect.Descriptor.index x d in
    let output = nest (!^ "Exception.run" ^^ OCaml.int n ^^ to_coq true e ^^ !^ "tt") in
    Pp.parens paren output
  | Return (_, e) -> Pp.parens paren @@ nest (!^ "ret" ^^ to_coq true e)
  | Bind (_, e1, x, e2) ->
    Pp.parens paren @@ nest (
      !^ "let!" ^^ (match x with
        | None -> !^ "_"
        | Some x -> CoqName.to_coq x) ^-^ !^ " :=" ^^
        to_coq false e1 ^^ !^ "in" ^^ newline ^^
      to_coq false e2)
  | Lift (_, d1, d2, e) ->
    let (bs, union_lift) = Effect.Lift.compute d1 d2 in
    let coq = to_coq true e in
    let coq = match union_lift with
      | Some (Effect.Lift.Lift (in_list, n)) ->
        Pp.parens (paren || is_some bs) @@ nest @@
          !^ "@Union.lift _ _ _" ^^ in_list ^^ OCaml.int n ^^ coq
      | Some (Effect.Lift.Mix (in_list, out_list)) ->
        Pp.parens (paren || is_some bs) @@ nest @@
          !^ "@Union.mix _ _ _ _" ^^ in_list ^^
          to_coq_list (List.map OCaml.int out_list) ^-^ !^ "%nat" ^^
          !^ "eq_refl eq_refl" ^^ coq
      | Some (Effect.Lift.Inject n) ->
        Pp.parens (paren || is_some bs) @@ nest @@
          !^ "Union.inject" ^^ OCaml.int n ^^ coq
      | None -> coq in
    match bs with
    | Some bs ->
      Pp.parens paren @@ nest @@
        !^ "lift" ^^ to_coq_list (List.map (fun _ -> !^ "_") bs) ^^
        double_quotes (separate empty
          (List.map (fun b -> if b then !^ "1" else !^ "0") bs)) ^^ coq
    | None -> coq
