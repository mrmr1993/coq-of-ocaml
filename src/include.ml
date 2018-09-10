open SmartPrint

type t = BoundName.t

let pp (incl : t) : SmartPrint.t =
  nest (!^ "Include" ^^ (BoundName.pp incl))

let of_ocaml (env : 'a FullEnvi.t) (loc : Loc.t) (path : Path.t) : t =
  let path = PathName.of_path loc path in
  FullEnvi.Module.bound loc path env

let update_env (loc : Loc.t) (incl : t) (env : unit FullEnvi.t)
  : unit FullEnvi.t =
  let mod_body = FullEnvi.Module.find loc incl env in
  FullEnvi.include_module (fun _ _ _ -> ()) mod_body env

let update_env_with_effects (loc : Loc.t) (incl : t)
  (env : Effect.Type.t FullEnvi.t) : Effect.Type.t FullEnvi.t =
  let mod_body = FullEnvi.Module.find loc incl env in
  let update_effects f env v =
    let v = v |> Effect.Type.map (fun x ->
      { x with BoundName.full_path = f x.BoundName.full_path }) in
    FullEnvi.localize_type env v in
  FullEnvi.include_module update_effects mod_body env

let of_interface (path : PathName.t) (env : 'a FullEnvi.t) =
  let bound_module = FullEnvi.Module.bound Loc.Unknown path env in
  update_env_with_effects Loc.Unknown bound_module env

(** Pretty-print an include construct to Coq. *)
let to_coq (incl : t): SmartPrint.t =
  nest (!^ "Include" ^^ BoundName.to_coq incl ^-^ !^ ".")
