(** Types for the effects. *)
open SmartPrint

module PureType = struct
  type t =
  | Variable of Name.t
  | Arrow of t * t
  | Tuple of t list
  | Apply of BoundName.t * t list

let rec pp (typ : t) : SmartPrint.t =
  match typ with
  | Variable x -> Name.pp x
  | Arrow (typ1, typ2) -> nest @@ parens (pp typ1 ^^ !^ "->" ^^ pp typ2)
  | Tuple typs -> nest @@ parens (separate (space ^^ !^ "*" ^^ space) (List.map pp typs))
  | Apply (x, typs) ->
    nest @@ Pp.parens (typs <> []) @@
      separate (!^ "," ^^ space) (BoundName.pp x :: List.map pp typs)

let first_param (typ : t) : t =
  match typ with
  | Apply (_, typ :: _) -> typ
  | _ -> Variable "_"

let rec to_coq (paren : bool) (typ : t) : SmartPrint.t =
  match typ with
  | Variable x -> Name.to_coq x
  | Arrow (typ_x, typ_y) ->
    Pp.parens paren @@ nest (to_coq true typ_x ^^ !^ "->" ^^ to_coq false typ_y)
  | Tuple typs ->
    (match typs with
    | [] -> !^ "unit"
    | _ ->
      Pp.parens paren @@ nest @@ separate (space ^^ !^ "*" ^^ space)
        (List.map (to_coq true) typs))
  | Apply (path, typs) ->
    Pp.parens (paren && typs <> []) @@ nest @@ separate space
      (BoundName.to_coq path :: List.map (to_coq true) typs)

let rec map (f : BoundName.t -> BoundName.t) (typ : t) : t =
  match typ with
  | Variable x -> Variable x
  | Arrow (typ_x, typ_y) -> Arrow (map f typ_x, map f typ_y)
  | Tuple typs -> Tuple (List.map (map f) typs)
  | Apply (path, typs) -> Apply (f path, List.map (map f) typs)
end


module Descriptor = struct
  module Id = struct
    type t =
      | Type of BoundName.t * PureType.t list (* Mirrors PureType.Apply *)

    let ether (x : BoundName.t) : t = Type (x, [])

    let map (f : BoundName.t -> BoundName.t) (x : t) =
      match x with
      | Type (x, typs) -> Type (f x, List.map (PureType.map f) typs)

    let bound_name (x : t) : BoundName.t =
      match x with
      | Type (x, _) -> x
  end
  module Set = Set.Make (struct
      type t = Id.t

      (* Compare on the base name first, for better stability across modules. *)
      let compare x y =
        match x, y with
        | Id.Type ({path_name={base=a}}, _),
          Id.Type ({path_name={base=b}}, _) ->
          let cmp = compare a b in
          if cmp == 0 then compare x y else cmp

    end)
  type t = Set.t

  let pp (d : t) : SmartPrint.t =
    Set.elements d |> OCaml.list (fun id ->
      match id with
      | Id.Type (x, typs) -> PureType.pp (PureType.Apply (x, typs)))

  let pure : t = Set.empty

  let is_pure (d : t) : bool = Set.is_empty d

  let eq (d1 : t) (d2 : t) : bool = Set.equal d1 d2

  let singleton (id : Id.t) : t = Set.singleton id

  let union (ds : t list) : t =
    List.fold_left (fun d1 d2 -> Set.fold Set.add d1 d2) pure ds

  let mem (x : BoundName.t) (d : t) : bool =
    Set.exists (fun y -> x = Id.bound_name y) d

  let remove (x : BoundName.t) (d : t) : t =
    Set.filter (fun y -> x <> Id.bound_name y) d

  let filter (f : Id.t -> bool) (d : t) : t = Set.filter f d

  let elements (d : t) : BoundName.t list =
    Set.elements d |> List.map Id.bound_name

  let index (x : BoundName.t) (d : t) : int =
    let rec find_index l f =
      match l with
      | [] -> 0
      | x :: xs -> if f x then 0 else 1 + find_index xs f in
    find_index (Set.elements d) (fun y -> x = Id.bound_name y)

  let to_coq (d : t) : SmartPrint.t =
    Set.elements d |> OCaml.list (fun x ->
      match x with
      | Id.Type (x, typs) ->
        PureType.to_coq false (PureType.Apply (x, typs)))

  let subset_to_coq (d1 : t) (d2 : t) : SmartPrint.t =
    let rec aux xs1 xs2 : bool list =
      match (xs1, xs2) with
      | ([], _) -> List.map (fun _ -> false) xs2
      | (x1 :: xs1', x2 :: xs2') ->
        if x1 = x2 then
          true :: aux xs1' xs2'
        else
          false :: aux xs1 xs2'
      | (_ :: _, []) ->
        failwith "Must be a subset to display the subset." in
    let bs = aux (Set.elements d1) (Set.elements d2) in
    brakets (separate (!^ ";") (List.map (fun _ -> !^ "_") bs)) ^^
    double_quotes (separate empty
      (List.map (fun b -> if b then !^ "1" else !^ "0") bs))

  let depth_lift (d : t) : t =
    Set.map (Id.map BoundName.depth_lift) d

  let leave_prefix (name : Name.t option) (d : t) : t =
    Set.map (Id.map (BoundName.leave_prefix name)) d

  let resolve_open (name_list : Name.t list) (d : t) : t =
    Set.map (Id.map (BoundName.resolve_open name_list)) d
end

module Type = struct
  type t =
    | Pure
    | Arrow of Descriptor.t * t

  let rec pp (typ : t) : SmartPrint.t =
    match typ with
    | Pure -> !^ "."
    | Arrow (d, typ) -> nest (
      !^ "." ^^
      (if Descriptor.is_pure d then
        !^ "->"
      else
        !^ "-" ^-^ Descriptor.pp d ^-^ !^ "->") ^^
      pp typ)

  let rec is_pure (typ : t) : bool =
    match typ with
    | Pure -> true
    | Arrow (d, typ) -> Descriptor.is_pure d && is_pure typ

  let rec compress (typ : t) : t =
    if is_pure typ then
      Pure
    else
      match typ with
      | Pure -> Pure
      | Arrow (d, typ) -> Arrow (d, compress typ)

  let rec eq (typ1 : t) (typ2 : t) : bool =
    match (typ1, typ2) with
    | (Pure, _) -> is_pure typ2
    | (_, Pure) -> is_pure typ1
    | (Arrow (d1, typ1), Arrow (d2, typ2)) ->
      (Descriptor.eq d1 d2) && eq typ1 typ2

  let map (f : int -> Descriptor.t -> Descriptor.t) (x : t) =
    let rec map i x =
      match x with
      | Arrow (desc, x) -> Arrow (f i desc, map (i+1) x)
      | Pure -> Pure in
    map 0 x

  let rec return_descriptor (typ : t) (nb_args : int) : Descriptor.t =
    if nb_args = 0 then
      Descriptor.pure
    else
      match typ with
      | Pure -> Descriptor.pure
      | Arrow (d, typ) ->
        Descriptor.union [d; return_descriptor typ (nb_args - 1)]

  let rec return_type (typ : t) (nb_args : int) : t =
    if nb_args = 0 then
      typ
    else
      match typ with
      | Pure -> Pure
      | Arrow (_, typ) -> return_type typ (nb_args - 1)

  let union (typs : t list) : t =
    let rec aux typ1 typ2 =
      match (typ1, typ2) with
      | (Pure, _) -> if is_pure typ2 then Pure else typ2
      | (_, Pure) -> if is_pure typ1 then Pure else typ1
      | (Arrow (d1, typ1), Arrow (d2, typ2)) ->
        Arrow (Descriptor.union [d1; d2], aux typ1 typ2) in
    List.fold_left aux Pure typs

  let rec depth_lift (typ : t) : t =
    match typ with
    | Pure -> Pure
    | Arrow (d, typ) -> Arrow (Descriptor.depth_lift d, depth_lift typ)

  let rec leave_prefix (x : Name.t option) (typ : t) : t =
    match typ with
    | Pure -> Pure
    | Arrow (d, typ) -> Arrow (Descriptor.leave_prefix x d, leave_prefix x typ)

  let rec resolve_open (x : Name.t list) (typ : t) : t =
    match typ with
    | Pure -> Pure
    | Arrow (d, typ) -> Arrow (Descriptor.resolve_open x d, resolve_open x typ)
end

type t = { descriptor : Descriptor.t; typ : Type.t }

let pp (effect : t) : SmartPrint.t =
  nest (!^ "Effect" ^^ OCaml.tuple [
    Descriptor.pp effect.descriptor; Type.pp effect.typ])

let function_typ (args : 'a list) (body_effect : t) : Type.t =
  match args with
  | [] -> body_effect.typ
  | _ :: args ->
    List.fold_left (fun effect_typ _ ->
      Type.Arrow (Descriptor.pure, effect_typ))
      (Type.Arrow
          (body_effect.descriptor, body_effect.typ))
      args

let pure : t = {
  descriptor = Descriptor.pure;
  typ = Type.Pure }

let union (effects : t list) : t =
  { descriptor =
      Descriptor.union @@ List.map (fun effect -> effect.descriptor) effects;
    typ = Type.union (List.map (fun effect -> effect.typ) effects) }
