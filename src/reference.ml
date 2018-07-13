open Typedtree
open SmartPrint

type 'a t = {
  name : CoqName.t;
  state_name : CoqName.t;
  typ : Type.t;
  expr : 'a Exp.t }

let pp (pp_a : 'a -> SmartPrint.t) (r : 'a t) : SmartPrint.t =
  nest (!^ "Reference" ^^
    OCaml.tuple [CoqName.pp r.name; CoqName.pp r.state_name; Type.pp r.typ;
      Exp.pp pp_a r.expr])

let is_reference (loc : Loc.t) (cases : value_binding list) : bool =
  match cases with
  | [{ vb_expr = {
    exp_desc = Texp_apply ({exp_desc = Texp_ident (path, _, _)}, [_]) }}]
    when PathName.of_path loc path = PathName.of_name ["Pervasives"] "ref" ->
    true
  | _ -> false

let of_ocaml (env : unit FullEnvi.t) (loc : Loc.t) (cases : value_binding list)
  : 'a t =
  match cases with
  | [{ vb_pat = { pat_desc = Tpat_var (x, _) };
    vb_expr = { exp_type = {Types.desc = Types.Tconstr (_, [typ], _) };
                exp_desc = Texp_apply (_, [(_, Some expr)]) }}] ->
    let name = Name.of_ident x in
    let coq_name = (FullEnvi.Var.resolve [] name env).base in
    let state_name = name ^ "_state" in
    let coq_state_name = (FullEnvi.Descriptor.resolve [] state_name env).base in
    { name = CoqName.of_names name coq_name;
      state_name = CoqName.of_names state_name coq_state_name;
      typ = Type.of_type_expr env loc typ;
      expr = Exp.of_expression env Name.Map.empty expr }
  | _ -> Error.raise loc "This kind of reference definition is not handled."

let update_env (update_exp : unit FullEnvi.t -> 'a Exp.t -> 'b Exp.t)
  (r : 'a t) (env : unit FullEnvi.t) : unit FullEnvi.t * 'b t =
  let (name, coq_name) = CoqName.assoc_names r.name in
  let (state_name, coq_state_name) = CoqName.assoc_names r.state_name in
  let env = env
  |> FullEnvi.Var.assoc [] name coq_name ()
  |> FullEnvi.Descriptor.assoc [] state_name coq_state_name in
  (env, {r with expr = update_exp env r.expr})

let update_env_with_effects (r : (Loc.t * Type.t) t)
  (env : Effect.Type.t FullEnvi.t) (id : Effect.Descriptor.Id.t)
  : Effect.Type.t FullEnvi.t * (Loc.t * Effect.t) t =
  let (name, coq_name) = CoqName.assoc_names r.name in
  let (state_name, coq_state_name) = CoqName.assoc_names r.state_name in
  let env = env
  |> FullEnvi.Var.assoc [] name coq_name Effect.Type.Pure
  |> FullEnvi.Descriptor.assoc [] state_name coq_state_name in
  (env, {r with expr = Exp.effects env r.expr})

let to_coq (r : 'a t) : SmartPrint.t =
  nest (!^ "Definition" ^^ CoqName.to_coq r.name ^^
    !^ ":" ^^ !^ "OCaml.Effect.State.t" ^^ Type.to_coq true r.typ ^^ !^ ":=" ^^
    !^ "OCaml.Effect.State.init" ^^ Exp.to_coq true r.expr ^-^ !^ ".")
  ^^ newline ^^
  nest (!^ "Definition" ^^ CoqName.to_coq r.state_name ^^ !^ ":=" ^^
    !^ "nat" ^-^ !^ ".")
