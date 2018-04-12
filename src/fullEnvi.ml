open SmartPrint

type 'a t = {
  vars : 'a Envi.t;
  leave_prefix_vars : Name.t -> 'a -> 'a;
  typs : unit Envi.t;
  descriptors: unit Envi.t;
  constructors : unit Envi.t;
  fields : unit Envi.t }

let pp (env : 'a t) : SmartPrint.t =
  group (
    !^ "vars:" ^^ nest (Envi.pp env.vars) ^^ newline ^^
    !^ "typs:" ^^ nest (Envi.pp env.typs) ^^ newline ^^
    !^ "descriptors:" ^^ nest (Envi.pp env.descriptors) ^^ newline ^^
    !^ "constructors:" ^^ nest (Envi.pp env.constructors) ^^ newline ^^
    !^ "fields:" ^^ nest (Envi.pp env.fields))

let empty (leave_prefix_vars : Name.t -> 'a -> 'a) : 'a t = {
  vars = Envi.empty;
  leave_prefix_vars = leave_prefix_vars;
  typs = Envi.empty;
  descriptors = Envi.empty;
  constructors = Envi.empty;
  fields = Envi.empty }

let add_var (path : Name.t list) (base : Name.t) (v : 'a) (env : 'a t)
  : 'a t =
  { env with vars = Envi.add (PathName.of_name path base) v env.vars }

let add_typ (path : Name.t list) (base : Name.t) (env : 'a t)
  : 'a t =
  { env with typs = Envi.add (PathName.of_name path base) () env.typs }

let add_descriptor (path : Name.t list) (base : Name.t) (env : 'a t)
  : 'a t =
  { env with descriptors =
    Envi.add (PathName.of_name path base) () env.descriptors }

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
        (Envi.bound_name Loc.Unknown (PathName.of_name path base) env.descriptors),
      Effect.Type.Pure) in
  add_var path ("raise_" ^ base) effect_typ env

let add_constructor (path : Name.t list) (base : Name.t) (env : 'a t)
  : 'a t =
  { env with constructors =
    Envi.add (PathName.of_name path base) () env.constructors }

let add_field (path : Name.t list) (base : Name.t) (env : 'a t)
  : 'a t =
  { env with fields =
    Envi.add (PathName.of_name path base) () env.fields }

let enter_module (env : 'a t) : 'a t =
  { vars = Envi.enter_module env.vars;
    leave_prefix_vars = env.leave_prefix_vars;
    typs = Envi.enter_module env.typs;
    descriptors = Envi.enter_module env.descriptors;
    constructors = Envi.enter_module env.constructors;
    fields = Envi.enter_module env.fields }

let leave_module (module_name : Name.t) (env : 'a t) : 'a t =
  let leave_prefix_unit = fun _ () -> () in
  { vars = Envi.leave_module env.vars env.leave_prefix_vars module_name;
    leave_prefix_vars = env.leave_prefix_vars;
    typs = Envi.leave_module env.typs leave_prefix_unit module_name;
    descriptors =
      Envi.leave_module env.descriptors leave_prefix_unit module_name;
    constructors =
      Envi.leave_module env.constructors leave_prefix_unit module_name;
    fields = Envi.leave_module env.fields leave_prefix_unit module_name }

let open_module (module_name : Name.t list) (env : 'a t) : 'a t =
  { vars = Envi.open_module env.vars module_name;
    leave_prefix_vars = env.leave_prefix_vars;
    typs = Envi.open_module env.typs module_name;
    descriptors = Envi.open_module env.descriptors module_name;
    constructors = Envi.open_module env.constructors module_name;
    fields = Envi.open_module env.fields module_name }

module ModList = struct
  type 'a t = 'a Envi.Mod.t list

  let pp (env : 'a t) : SmartPrint.t =
    OCaml.list Envi.Mod.pp env

  let empty : 'a t = [Envi.Mod.empty]

  let add_var (path : Name.t list) (base : Name.t) (v : 'a) (env : 'a t)
    : 'a t =
    match env with
    | m :: env -> Envi.Mod.Vars.add (PathName.of_name path base) v m :: env
    | [] -> failwith "The environment must be a non-empty list."

  let add_typ (path : Name.t list) (base : Name.t) (env : 'a t)
    : 'a t =
    match env with
    | m :: env -> Envi.Mod.Typs.add (PathName.of_name path base) m :: env
    | [] -> failwith "The environment must be a non-empty list."

  let add_descriptor (path : Name.t list) (base : Name.t) (env : 'a t)
    : 'a t =
    match env with
    | m :: env -> Envi.Mod.Descriptors.add (PathName.of_name path base) m :: env
    | [] -> failwith "The environment must be a non-empty list."

  let add_constructor (path : Name.t list) (base : Name.t) (env : 'a t)
    : 'a t =
    match env with
    | m :: env -> Envi.Mod.Constructors.add (PathName.of_name path base) m :: env
    | [] -> failwith "The environment must be a non-empty list."

  let add_field (path : Name.t list) (base : Name.t) (env : 'a t)
    : 'a t =
    match env with
    | m :: env -> Envi.Mod.Fields.add (PathName.of_name path base) m :: env
    | [] -> failwith "The environment must be a non-empty list."

  let enter_module (env : 'a t) : 'a t = Envi.Mod.empty :: env

  let open_module (module_name : Name.t list) (env : 'a t) : 'a t =
    match env with
    | m :: env -> Envi.Mod.open_module m module_name :: env
    | _ -> failwith "You should have entered in at least one module."

  let leave_module (module_name : Name.t) (prefix : Name.t -> 'a -> 'a)
    (env : 'a t) : 'a t =
    match env with
    | m1 :: m2 :: env ->
      let m = Envi.Mod.close_module module_name prefix m1 m2 in
      m :: env
    | _ -> failwith "You should have entered in at least one module."

  let rec find_first (f : 'a -> 'b option) (l : 'a list) : 'b option =
    match l with
    | [] -> None
    | x :: l ->
      (match f x with
      | None -> find_first f l
      | y -> y)

  let rec bound_name_opt (find : PathName.t -> 'a Envi.Mod.t -> bool)
    (x : PathName.t) (env : 'a t) : BoundName.t option =
    match env with
    | m :: env ->
      if find x m then
        Some { BoundName.path_name = x; BoundName.depth = 0 }
      else
        m.Envi.Mod.opens |> find_first (fun path ->
          let x = { x with PathName.path = path @ x.PathName.path } in
          match bound_name_opt find x env with
          | None -> None
          | Some name -> Some { name with BoundName.depth = name.BoundName.depth + 1 })
    | [] -> None

  let bound_name (find : PathName.t -> 'a Envi.Mod.t -> bool) (loc : Loc.t)
    (x : PathName.t) (env : 'a t) : BoundName.t =
    match bound_name_opt find x env with
    | Some name -> name
    | None ->
      let message = PathName.pp x ^^ !^ "not found." in
      Error.raise loc (SmartPrint.to_string 80 2 message)

  let bound_var (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
    bound_name Envi.Mod.Vars.mem loc x env

  let bound_typ (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
    bound_name Envi.Mod.Typs.mem loc x env

  let bound_descriptor (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
    bound_name Envi.Mod.Descriptors.mem loc x env

  let bound_constructor (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
    bound_name Envi.Mod.Constructors.mem loc x env

  let bound_field (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
    bound_name Envi.Mod.Fields.mem loc x env

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

  let rec find_var (x : BoundName.t) (env : 'a t) (open_lift : 'a -> 'a) : 'a =
    let m =
      try List.nth env x.BoundName.depth with
      | Failure _ -> raise Not_found in
    let rec iterate_open_lift v n =
      if n = 0 then
        v
      else
        iterate_open_lift (open_lift v) (n - 1) in
    let v = Envi.Mod.Vars.find x.BoundName.path_name m in
    iterate_open_lift v x.BoundName.depth

  let fresh_var  (prefix : string) (v : 'a) (env : 'a t) : Name.t * 'a t =
    match env with
    | m :: env ->
      let (name, m) = Envi.Mod.Vars.fresh prefix v m in
      (name, m :: env)
    | [] -> failwith "The environment must be a non-empty list."

  let rec map (f : 'a -> 'b) (env : 'a t) : 'b t =
    match env with
    | m :: env -> Envi.Mod.Vars.map f m :: map f env
    | [] -> []
end
