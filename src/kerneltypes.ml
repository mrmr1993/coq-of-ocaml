module Value = struct
  type 'a t =
    | Variable of 'a
    | Function of 'a * Effect.PureType.t
    | Type
    | Descriptor
    | Exception of PathName.t
    | Constructor of Effect.PureType.t * Effect.PureType.t list
    | Field of Effect.PureType.t * Effect.PureType.t

  let map (f : 'a -> 'b) (v : 'a t) : 'b t =
    match v with
    | Variable a -> Variable (f a)
    | Function (a, typ) -> Function (f a, typ)
    | Type -> Type
    | Descriptor -> Descriptor
    | Exception raise_name -> Exception raise_name
    | Constructor (typ, typs) -> Constructor (typ, typs)
    | Field (record_typ, typ) -> Field (record_typ, typ)

  let to_string (v : 'a t) : string =
    match v with
    | Variable _ -> "variable"
    | Function _ -> "function"
    | Type -> "type"
    | Descriptor -> "descriptor"
    | Exception _ -> "exception"
    | Constructor _ -> "constructor"
    | Field _ -> "field"
end
