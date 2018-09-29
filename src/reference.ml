open Typedtree
open SmartPrint

type 'a t = {
  name : CoqName.t;
  state_name : CoqName.t;
  effect : Effect.t;
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
    let state_name = name ^ "_state" in
    let (name, _, env) = FullEnvi.Var.create name () env in
    let (state_name, bound_state, env) =
      FullEnvi.Descriptor.fresh state_name () env in
    let state = FullEnvi.Descriptor.bound loc
      (PathName.of_name ["OCaml"; "Effect"; "State"] "state") env in
    let typ = Type.of_type_expr env loc typ in
    let descriptor = Effect.Descriptor.union [
      Effect.Descriptor.singleton state [Type.pure_type typ];
      Effect.Descriptor.singleton bound_state [];
    ] in
    let effect = { Effect.typ = Effect.Type.to_type @@ Effect.Type.Pure; descriptor } in
    { name = name;
      state_name = state_name;
      effect;
      typ = typ;
      expr = Exp.of_expression env Name.Map.empty expr }
  | _ -> Error.raise loc "This kind of reference definition is not handled."

let update_env (update_exp : unit FullEnvi.t -> 'a Exp.t -> 'b Exp.t)
  (r : 'a t) (env : unit FullEnvi.t) : unit FullEnvi.t * 'b t =
  let env = env
    |> FullEnvi.Descriptor.assoc r.state_name ()
    |> FullEnvi.Var.assoc r.name () in
  (env, {r with expr = update_exp env r.expr})

let update_env_with_effects (r : (Loc.t * Type.t) t)
  (env : Effect.t FullEnvi.t)
  : Effect.t FullEnvi.t * (Loc.t * Effect.t) t =
  let env = env
    |> FullEnvi.Descriptor.assoc r.state_name ()
    |> FullEnvi.Var.assoc r.name r.effect in
  (env, {r with expr = Exp.effects env r.expr})

let to_coq (r : 'a t) : SmartPrint.t =
  nest (!^ "Definition" ^^ CoqName.to_coq r.state_name ^^ !^ ":=" ^^
    !^ "OCaml.Effect.State.global_state" ^-^ !^ ".")
  ^^ newline ^^
  nest (!^ "Definition" ^^ CoqName.to_coq r.name ^^
    !^ ": M [ OCaml.Effect.State.state" ^^ Type.to_coq true r.typ ^-^ !^ ";" ^^
      CoqName.to_coq r.state_name ^^ !^ "]" ^^
    group (!^ "(OCaml.Effect.State.t" ^^ Type.to_coq true r.typ ^-^ !^ ") :=") ^^
    !^ "OCaml.Effect.State.global" ^^ Exp.to_coq true r.expr ^-^ !^ ".")
