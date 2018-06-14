open SmartPrint
open Utils

type 'a t = 'a Mod.t list

let pp (env : 'a t) : SmartPrint.t =
  OCaml.list Mod.pp env

let empty : 'a t = [Mod.empty]

let add_var (path : Name.t list) (base : Name.t) (v : 'a) (env : 'a t)
  : 'a t =
  match env with
  | m :: env -> Mod.Vars.add (PathName.of_name path base) v m :: env
  | [] -> failwith "The environment must be a non-empty list."

let add_typ (path : Name.t list) (base : Name.t) (env : 'a t)
  : 'a t =
  match env with
  | m :: env -> Mod.Typs.add (PathName.of_name path base) m :: env
  | [] -> failwith "The environment must be a non-empty list."

let add_descriptor (path : Name.t list) (base : Name.t) (env : 'a t)
  : 'a t =
  match env with
  | m :: env -> Mod.Descriptors.add (PathName.of_name path base) m :: env
  | [] -> failwith "The environment must be a non-empty list."

let add_constructor (path : Name.t list) (base : Name.t) (env : 'a t)
  : 'a t =
  match env with
  | m :: env -> Mod.Constructors.add (PathName.of_name path base) m :: env
  | [] -> failwith "The environment must be a non-empty list."

let add_field (path : Name.t list) (base : Name.t) (env : 'a t)
  : 'a t =
  match env with
  | m :: env -> Mod.Fields.add (PathName.of_name path base) m :: env
  | [] -> failwith "The environment must be a non-empty list."

let add_module (path : Name.t list) (base : Name.t) (v : 'a Mod.t) (env : 'a t)
  : 'a t =
  match env with
  | m :: env -> Mod.Modules.add (PathName.of_name path base) v m :: env
  | [] -> failwith "The environment must be a non-empty list."

let enter_module (env : 'a t) : 'a t = Mod.empty :: env

let open_module (module_name : Name.t list) (env : 'a t) : 'a t =
  match env with
  | m :: env -> Mod.open_module m module_name :: env
  | _ -> failwith "You should have entered in at least one module."

let open_external_module (module_name : Name.t list) (env : 'a t) : 'a t =
  match env with
  | m :: env -> Mod.open_external_module m module_name :: env
  | _ -> failwith "You should have entered in at least one module."

let rec external_opens (env : 'a t) : Name.t list list =
  match env with
  | m :: env -> m.external_opens @ external_opens env
  | [] -> []

let leave_module (module_name : Name.t) (prefix : Name.t -> 'a -> 'a)
  (env : 'a t) : 'a t =
  match env with
  | m1 :: m2 :: env ->
    let m = Mod.finish_module module_name prefix m1 m2 in
    m :: env
  | _ -> failwith "You should have entered in at least one module."

let rec find_first (f : 'a -> 'b option) (l : 'a list) : 'b option =
  match l with
  | [] -> None
  | x :: l ->
    (match f x with
    | None -> find_first f l
    | y -> y)

let rec bound_name_opt (find : PathName.t -> 'a Mod.t -> bool)
  (x : PathName.t) (env : 'a t) : BoundName.t option =
  match env with
  | m :: env ->
    if find x m then
      Some { BoundName.path_name = x; BoundName.depth = 0 }
    else
      m.Mod.opens |> find_first (fun path ->
        let x = { x with PathName.path = path @ x.PathName.path } in
        bound_name_opt find x env |> option_map (fun name ->
          { name with BoundName.depth = name.BoundName.depth + 1 }))
  | [] -> None

let bound_name (find : PathName.t -> 'a Mod.t -> bool) (loc : Loc.t)
  (x : PathName.t) (env : 'a t) : BoundName.t =
  match bound_name_opt find x env with
  | Some name -> name
  | None ->
    let message = PathName.pp x ^^ !^ "not found." in
    Error.raise loc (SmartPrint.to_string 80 2 message)

let bound_var (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
  bound_name Mod.Vars.mem loc x env

let bound_typ (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
  bound_name Mod.Typs.mem loc x env

let bound_descriptor (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
  bound_name Mod.Descriptors.mem loc x env

let bound_constructor (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
  bound_name Mod.Constructors.mem loc x env

let bound_field (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
  bound_name Mod.Fields.mem loc x env

let bound_module_opt (x : PathName.t) (env : 'a t) : BoundName.t option =
  bound_name_opt Mod.Modules.mem x env

let bound_module (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
  bound_name Mod.Modules.mem loc x env

let add_exception (path : Name.t list) (base : Name.t) (env : unit t) : unit t =
  env
  |> add_descriptor path base
  |> add_var path ("raise_" ^ base) ()

let add_exception_with_effects (path : Name.t list) (base : Name.t)
  (id : Effect.Descriptor.Id.t) (env : Effect.Type.t t)
  : Effect.Type.t t =
  let env = add_descriptor path base env in
  let effect_typ =
    Effect.Type.Arrow (
      Effect.Descriptor.singleton
        id
        (bound_descriptor Loc.Unknown (PathName.of_name path base) env),
      Effect.Type.Pure) in
  add_var path ("raise_" ^ base) effect_typ env

let rec find_bound_name (find : PathName.t -> 'a Mod.t -> 'b) (x : BoundName.t)
  (env : 'a t) (open_lift : 'b -> 'b) : 'b =
  let m =
    try List.nth env x.BoundName.depth with
    | Failure _ -> raise Not_found in
  let rec iterate_open_lift v n =
    if n = 0 then
      v
    else
      iterate_open_lift (open_lift v) (n - 1) in
  let v = find x.BoundName.path_name m in
  iterate_open_lift v x.BoundName.depth

let find_var (x : BoundName.t) (env : 'a t) (open_lift : 'a -> 'a) : 'a =
  find_bound_name Mod.Vars.find x env open_lift

let find_module (x : BoundName.t) (env : 'a t)
  (open_lift : 'a Mod.t -> 'a Mod.t) : 'a Mod.t =
  find_bound_name Mod.Modules.find x env open_lift

let fresh_var  (prefix : string) (v : 'a) (env : 'a t) : Name.t * 'a t =
  match env with
  | m :: env ->
    let (name, m) = Mod.Vars.fresh prefix v m in
    (name, m :: env)
  | [] -> failwith "The environment must be a non-empty list."

let rec map (f : 'a -> 'b) (env : 'a t) : 'b t =
  match env with
  | m :: env -> Mod.map f m :: map f env
  | [] -> []

let include_module (loc : Loc.t) (x : 'a Mod.t) (env : 'a t) : 'a t =
  match env with
  | m :: env ->
      (try Mod.include_module x m :: env with
      | Mod.NameConflict (typ, name) ->
        let message = !^ "Could not include module: the" ^^ !^ typ ^^
          PathName.pp name ^^ !^ "is already declared." in
        Error.raise loc (SmartPrint.to_string 80 2 message))
  | [] -> failwith "The environment must be a non-empty list."
