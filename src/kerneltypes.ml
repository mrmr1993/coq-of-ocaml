module Type = struct
  type 'a t' =
    | Variable of Name.t
    | Arrow of 'a t' * 'a t'
    | Tuple of 'a t' list
    | Apply of BoundName.t * 'a t' list
    | Monad of 'a * 'a t'
end

module TypeDefinition = struct
  type 'a t' =
    | Inductive of CoqName.t * Name.t list * (CoqName.t * 'a Type.t' list) list
    | Record of CoqName.t * Name.t list * (CoqName.t * 'a Type.t') list
    | Synonym of CoqName.t * Name.t list * 'a Type.t'
    | Abstract of CoqName.t * Name.t list
end
