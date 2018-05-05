open SmartPrint

type 'a t = 'a FullMod.t

let pp (env : 'a t) : SmartPrint.t = FullMod.pp env

let empty : 'a t = FullMod.empty

let add_var (path : Name.t list) (base : Name.t) (v : 'a) (env : 'a t)
  : 'a t =
  FullMod.add_var path base v env

let add_typ (path : Name.t list) (base : Name.t) (env : 'a t)
  : 'a t =
  FullMod.add_typ path base env

let add_descriptor (path : Name.t list) (base : Name.t) (env : 'a t)
  : 'a t =
  FullMod.add_descriptor path base env

let add_constructor (path : Name.t list) (base : Name.t) (env : 'a t)
  : 'a t =
  FullMod.add_constructor path base env

let add_field (path : Name.t list) (base : Name.t) (env : 'a t)
  : 'a t =
  FullMod.add_field path base env

let add_module (path : Name.t list) (base : Name.t) (v : 'a Mod.t) (env : 'a t)
  : 'a t =
  FullMod.add_module path base v env

let enter_module (env : 'a t) : 'a t = FullMod.enter_module env

let open_module (module_name : Name.t list) (env : 'a t) : 'a t =
  FullMod.open_module module_name env

let leave_module (module_name : Name.t) (prefix : Name.t -> 'a -> 'a)
  (env : 'a t) : 'a t =
  FullMod.leave_module module_name prefix env

let find_first (f : 'a -> 'b option) (l : 'a list) : 'b option =
  FullMod.find_first f l

let rec bound_name_opt (find : PathName.t -> 'a Mod.t -> bool)
  (x : PathName.t) (env : 'a t) : BoundName.t option =
  FullMod.bound_name_opt find x env

let bound_name (find : PathName.t -> 'a Mod.t -> bool) (loc : Loc.t)
  (x : PathName.t) (env : 'a t) : BoundName.t =
  FullMod.bound_name find loc x env

let bound_var (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
  FullMod.bound_var loc x env

let bound_typ (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
  FullMod.bound_typ loc x env

let bound_descriptor (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
  FullMod.bound_descriptor loc x env

let bound_constructor (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
  FullMod.bound_constructor loc x env

let bound_field (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
  FullMod.bound_field loc x env

let bound_module (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
  FullMod.bound_module loc x env

let add_exception (path : Name.t list) (base : Name.t) (env : unit t) : unit t =
  FullMod.add_exception path base env

let add_exception_with_effects (path : Name.t list) (base : Name.t)
  (id : Effect.Descriptor.Id.t) (env : Effect.Type.t t)
  : Effect.Type.t t =
  FullMod.add_exception_with_effects path base id env

let find_var (x : BoundName.t) (env : 'a t) (open_lift : 'a -> 'a) : 'a =
  FullMod.find_var x env open_lift

let find_module (x : BoundName.t) (env : 'a t)
  (open_lift : 'a Mod.t -> 'a Mod.t) : 'a Mod.t =
  FullMod.find_module x env open_lift

let fresh_var  (prefix : string) (v : 'a) (env : 'a t) : Name.t * 'a t =
  FullMod.fresh_var prefix v env

let map (f : 'a -> 'b) (env : 'a t) : 'b t =
  FullMod.map f env

let include_module (loc : Loc.t) (x : 'a Mod.t) (env : 'a t) : 'a t =
  FullMod.include_module loc x env
