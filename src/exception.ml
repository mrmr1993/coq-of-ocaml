open Typedtree
open SmartPrint

type t = {
  name : CoqName.t;
  raise_name : CoqName.t;
  typ : Type.t }

let pp (exn : t) : SmartPrint.t =
  nest (!^ "Exception" ^^
    OCaml.tuple [CoqName.pp exn.name; CoqName.pp exn.raise_name; Type.pp exn.typ])

let of_ocaml (env : unit FullEnvi.t) (loc : Loc.t)
  (exn : extension_constructor) : t =
  let name = Name.of_ident exn.ext_id in
  let typs =
    match exn.ext_type.Types.ext_args with
    | Types.Cstr_tuple typs -> typs
    | Types.Cstr_record _ -> Error.raise loc "Unhandled named constructor parameters." in
  let typ = Type.Tuple (typs |> List.map (fun typ -> Type.of_type_expr env loc typ)) in
  let (raise_name, _, env) =
    FullEnvi.Descriptor.fresh ("raise_" ^ name) () env in
  let (name, _, env) = FullEnvi.Var.create name () env in
  { name; raise_name; typ }

let update_env (exn : t) (env : unit FullEnvi.t) : unit FullEnvi.t =
  let raise_path = {PathName.path = FullEnvi.coq_path env;
    base = snd (CoqName.assoc_names exn.raise_name)} in
  env
  |> FullEnvi.Exception.assoc exn.name raise_path
  |> FullEnvi.Var.assoc exn.raise_name ()

let update_env_with_effects (exn : t) (env : Effect.t FullEnvi.t)
  : Effect.t FullEnvi.t =
  let raise_path = {PathName.path = FullEnvi.coq_path env;
    base = snd (CoqName.assoc_names exn.raise_name)} in
  let env = FullEnvi.Exception.assoc exn.name raise_path env in
  let bound_effect = FullEnvi.Descriptor.bound Loc.Unknown
    (PathName.of_name [] (CoqName.ocaml_name exn.name)) env in
  let effect_typ = Effect.Type.to_type @@
    Effect.Type.Arrow (
      Effect.Descriptor.singleton bound_effect [],
      Effect.Type.Pure) in
  FullEnvi.Var.assoc exn.raise_name (Effect.eff effect_typ) env

let to_coq (exn : t) : SmartPrint.t =
  !^ "Definition" ^^ CoqName.to_coq exn.name ^^ !^ ":=" ^^
    !^ "Effect.make" ^^ !^ "unit" ^^ Type.to_coq true exn.typ ^-^ !^ "." ^^
  newline ^^ newline ^^
  !^ "Definition" ^^ CoqName.to_coq exn.raise_name ^^ !^ "{A : Type}" ^^
    nest (parens (!^ "x" ^^ !^ ":" ^^ Type.to_coq false exn.typ)) ^^ !^ ":" ^^
    !^ "M" ^^ !^ "[" ^^ CoqName.to_coq exn.name ^^ !^ "]" ^^ !^ "A" ^^ !^ ":=" ^^
  newline ^^ indent (
    !^ "fun s => (inr (inl x), s).")
