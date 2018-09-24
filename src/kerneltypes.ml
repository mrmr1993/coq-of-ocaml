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

module Value = struct
  type 'a t =
    | Variable of 'a
    | Function of 'a * Effect.PureType.t
    | Type of TypeDefinition.t
    | Descriptor
    | Exception of PathName.t
    | Constructor of PathName.t * int
    | Field of PathName.t * int

  let map (f : 'a -> 'b) (v : 'a t) : 'b t =
    match v with
    | Variable a -> Variable (f a)
    | Function (a, typ) -> Function (f a, typ)
    | Type def -> Type def
    | Descriptor -> Descriptor
    | Exception raise_name -> Exception raise_name
    | Constructor (typ, index) -> Constructor (typ, index)
    | Field (typ, index) -> Field (typ, index)

  let to_string (v : 'a t) : string =
    match v with
    | Variable _ -> "variable"
    | Function _ -> "function"
    | Type _ -> "type"
    | Descriptor -> "descriptor"
    | Exception _ -> "exception"
    | Constructor _ -> "constructor"
    | Field _ -> "field"
end
