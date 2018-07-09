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
  let coq_name = (FullEnvi.resolve_descriptor [] name env).base in
  let raise_name = "raise_" ^ name in
  let coq_raise_name = (FullEnvi.resolve_var [] raise_name env).base in
  let typs =
    match exn.ext_type.Types.ext_args with
    | Types.Cstr_tuple typs -> typs
    | Types.Cstr_record _ -> Error.raise loc "Unhandled named constructor parameters." in
  let typ = Type.Tuple (typs |> List.map (fun typ -> Type.of_type_expr env loc typ)) in
  { name = CoqName.of_names name coq_name;
    raise_name = CoqName.of_names raise_name coq_raise_name;
    typ = typ}

let update_env (exn : t) (env : unit FullEnvi.t) : unit FullEnvi.t =
  let (name, coq_name) = CoqName.assoc_names exn.name in
  let (raise_name, coq_raise_name) = CoqName.assoc_names exn.raise_name in
  env
  |> FullEnvi.assoc_descriptor [] name coq_name
  |> FullEnvi.assoc_var [] raise_name coq_raise_name ()

let update_env_with_effects (exn : t) (env : Effect.Type.t FullEnvi.t)
  (id : Effect.Descriptor.Id.t) : Effect.Type.t FullEnvi.t =
  let (name, coq_name) = CoqName.assoc_names exn.name in
  let (raise_name, coq_raise_name) = CoqName.assoc_names exn.raise_name in
  let env = FullEnvi.assoc_descriptor [] name coq_name env in
  let effect_typ =
    Effect.Type.Arrow (
      Effect.Descriptor.singleton
        id
        (FullEnvi.bound_descriptor Loc.Unknown (PathName.of_name [] name) env),
      Effect.Type.Pure) in
  FullEnvi.assoc_var [] raise_name coq_raise_name effect_typ env

let to_coq (exn : t) : SmartPrint.t =
  !^ "Definition" ^^ CoqName.to_coq exn.name ^^ !^ ":=" ^^
    !^ "Effect.make" ^^ !^ "unit" ^^ Type.to_coq true exn.typ ^-^ !^ "." ^^
  newline ^^ newline ^^
  !^ "Definition" ^^ CoqName.to_coq exn.raise_name ^^ !^ "{A : Type}" ^^
    nest (parens (!^ "x" ^^ !^ ":" ^^ Type.to_coq false exn.typ)) ^^ !^ ":" ^^
    !^ "M" ^^ !^ "[" ^^ CoqName.to_coq exn.name ^^ !^ "]" ^^ !^ "A" ^^ !^ ":=" ^^
  newline ^^ indent (
    !^ "fun s => (inr (inl x), s).")
