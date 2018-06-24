open Typedtree
open SmartPrint

type 'a t = {
  name : Name.t;
  typ : Type.t;
  expr : 'a Exp.t }

let pp (pp_a : 'a -> SmartPrint.t) (r : 'a t) : SmartPrint.t =
  nest (!^ "Reference" ^^ OCaml.tuple
    [Name.pp r.name; Type.pp r.typ; Exp.pp pp_a r.expr])

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
    { name = Name.of_ident x;
      typ = Type.of_type_expr env loc typ;
      expr = Exp.of_expression env Name.Map.empty expr }
  | _ -> Error.raise loc "This kind of reference definition is not handled."

let update_env (update_exp : unit FullEnvi.t -> 'a Exp.t -> 'b Exp.t)
  (r : 'a t) (env : unit FullEnvi.t) : unit FullEnvi.t * 'b t =
  let env = env
  |> FullEnvi.add_var [] r.name ()
  |> FullEnvi.add_descriptor [] (r.name ^ "_state") in
  (env, {r with expr = update_exp env r.expr})

let update_env_with_effects (r : (Loc.t * Type.t) t)
  (env : Effect.Type.t FullEnvi.t) (id : Effect.Descriptor.Id.t)
  : Effect.Type.t FullEnvi.t * (Loc.t * Effect.t) t =
  let env = env
  |> FullEnvi.add_var [] r.name Effect.Type.Pure
  |> FullEnvi.add_descriptor [] (r.name ^ "_state") in
  (env, {r with expr = Exp.effects env r.expr})

let to_coq (r : 'a t) : SmartPrint.t =
  nest (!^ "Definition" ^^ Name.to_coq r.name ^^
    !^ ":" ^^ !^ "OCaml.Effect.State.t" ^^ Type.to_coq true r.typ ^^ !^ ":=" ^^
    !^ "OCaml.Effect.State.init" ^^ Exp.to_coq true r.expr ^-^ !^ ".")
  ^^ newline ^^
  nest (!^ "Definition" ^^ Name.to_coq r.name ^-^ !^ "_state" ^^ !^ ":=" ^^
    !^ "nat" ^-^ !^ ".")
