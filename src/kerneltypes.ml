module Type = struct
  type t =
    | Variable of Name.t
    | Arrow of t * t
    | Tuple of t list
    | Apply of BoundName.t * t list
    | Monad of Effect.Descriptor.t * t
end

module TypeDefinition = struct
  type t =
    | Inductive of CoqName.t * Name.t list * (CoqName.t * Type.t list) list
    | Record of CoqName.t * Name.t list * (CoqName.t * Type.t) list
    | Synonym of CoqName.t * Name.t list * Type.t
    | Abstract of CoqName.t * Name.t list
end
