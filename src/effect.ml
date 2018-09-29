(** Types for the effects. *)
open SmartPrint
open Yojson.Basic
open Utils

module PureType = struct
  include Kerneltypes.Type
  type t = unit Kerneltypes.Type.t'

  let pp (typ : t) : SmartPrint.t = CommonType.pp (fun () -> !^ "[]") typ

  let to_coq (paren : bool) (typ : t) : SmartPrint.t =
    CommonType.to_coq (fun () -> !^ "[]") paren typ

  let map (f : BoundName.t -> BoundName.t) (typ : t) : t = CommonType.map f typ

  let map_type_vars (vars_map : t Name.Map.t) (typ : t) : t =
    CommonType.map_vars (fun x -> Name.Map.find x vars_map) typ

  let has_type_vars (typ : t) : bool = CommonType.has_vars typ

  let to_json (typ : t) : json = CommonType.to_json (fun () -> `List []) typ

  let of_json (json : json) : t = CommonType.of_json (fun _ -> ()) json
end


module Descriptor = struct
  module Id = struct
    type t =
      | Type of BoundName.t * PureType.t list (* Mirrors PureType.Apply *)

    let map (f : BoundName.t -> BoundName.t) (x : t) =
      match x with
      | Type (x, typs) -> Type (f x, List.map (PureType.map f) typs)

    let bound_name (x : t) : BoundName.t =
      match x with
      | Type (x, _) -> x

    let map_type_vars (vars_map : PureType.t Name.Map.t) (x : t) : t =
      match x with
      | Type (x, typs) ->
        Type (x, List.map (PureType.map_type_vars vars_map) typs)
    let compare x y =
      match x, y with
      | Type (a, ta), Type (b, tb) ->
        let cmp = BoundName.stable_compare a b in
        if cmp == 0 then compare ta tb else cmp

    let to_puretype (x : t) : PureType.t =
      match x with | Type (x, typs) -> PureType.Apply (x, typs)

    let of_puretype (x : PureType.t) : t =
      match x with
      | PureType.Apply (x, typs) -> Type (x, typs)
      | _ -> failwith "Could not convert PureType to Descriptor.Id."

    let to_json (x : t) : json = PureType.to_json @@ to_puretype x

    let of_json (json : json) : t = of_puretype @@ PureType.of_json json
  end
  module IdSet = Set.Make (struct
      type t = Id.t
      let compare x y = Id.compare x y
    end)
  module BnSet = Set.Make (struct
      type t = BoundName.t
      let compare x y = BoundName.stable_compare x y
    end)

  (* NOTE: [unioned] should always represent how a statement accepts compound
     effects, while [compound] should hold these compound effects. *)
  type t = {
    unioned_arg : Name.t option;
    unioned : Id.t list;
    compound : IdSet.t;
    simple : BnSet.t
  }

  let pp (d : t) : SmartPrint.t =
    let id_els = d.unioned |> List.map (fun id ->
        match id with
        | Id.Type (x, typs) -> PureType.pp (PureType.Apply (x, typs))) in
    let bn_els = BnSet.elements d.simple |> List.map BoundName.pp in
    OCaml.list (fun x -> x) @@ id_els @ bn_els

  let pure : t = {
    unioned_arg = None;
    unioned = [];
    compound = IdSet.empty;
    simple = BnSet.empty
  }

  let is_pure (d : t) : bool =
    IdSet.is_empty d.compound && BnSet.is_empty d.simple

  let eq (d1 : t) (d2 : t) : bool =
    d1.unioned = d2.unioned && BnSet.equal d1.simple d2.simple

  let singleton (x : BoundName.t) (typs : PureType.t list) : t =
    if typs = [] then
      { unioned_arg = None;
        unioned = [];
        compound = IdSet.empty;
        simple = BnSet.singleton x
      }
    else
      { unioned_arg = None;
        unioned = [Id.Type (x, typs)];
        compound = IdSet.singleton (Id.Type (x, typs));
        simple = BnSet.empty
      }

  let union (ds : t list) : t =
    List.fold_left (fun d1 d2 ->
      let compound = IdSet.fold IdSet.add d1.compound d2.compound in
      { unioned_arg = None;
        unioned = IdSet.elements compound;
        compound = compound;
        simple = BnSet.fold BnSet.add d1.simple d2.simple
      }) pure ds

  let remove (x : BoundName.t) (d : t) : t =
    { d with simple = BnSet.remove x d.simple }

  let elements (d : t) : BoundName.t list = BnSet.elements d.simple

  let index (x : BoundName.t) (d : t) : int =
    let rec find_index l f =
      match l with
      | [] -> 0
      | x :: xs -> if f x then 0 else 1 + find_index xs f in
    find_index (BnSet.elements d.simple) (fun y -> x = y)

  let set_unioned_arg (arg : Name.t) (d : t) : t =
    { d with unioned_arg = Some arg }

  let should_carry (d : t) : bool = List.compare_length_with d.unioned 2 >= 0

  let to_coq (d : t) : SmartPrint.t =
    let should_carry = should_carry d in
    let id_els = d.unioned |> List.map (fun x ->
      match x with
      | Id.Type (x, typs) ->
        PureType.to_coq should_carry (PureType.Apply (x, typs))) in
    let id_els = if should_carry then
        [nest @@
          !^ "OCaml.Effect.Union.union" ^^
          (match d.unioned_arg with
           | Some arg -> Name.to_coq arg
           | None -> !^ "_") ^^
          OCaml.list (fun x -> x) id_els]
      else id_els in
    let bn_els = BnSet.elements d.simple |> List.map BoundName.to_coq in
    OCaml.list (fun x -> x) (id_els @ bn_els)

  let subset_to_bools (d1 : t) (d2 : t) : bool list =
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
    aux (BnSet.elements d1.simple) (BnSet.elements d2.simple)

  let map (f : BoundName.t -> BoundName.t) (d : t) : t =
    { d with
      unioned = List.map (Id.map f) d.unioned;
      compound = IdSet.map (Id.map f) d.compound;
      simple = BnSet.map f d.simple
    }

  let map_type_vars (vars_map : PureType.t Name.Map.t) (d : t) : t =
    { d with
      unioned = List.map (Id.map_type_vars vars_map) d.unioned;
      compound = IdSet.map (Id.map_type_vars vars_map) d.compound;
      simple = d.simple
    }

  let has_type_vars (d : t) : bool =
     d.compound |> IdSet.exists (fun (Type (x, typs)) ->
      List.exists PureType.has_type_vars typs)

  let to_json (d : t) : json =
    let unioned = List.map Id.to_json d.unioned in
    let simple = List.map BoundName.to_json @@ BnSet.elements d.simple in
    match unioned, simple with
    | [], [] -> `List []
    | [], _ -> `List simple
    | _, [] -> `List unioned
    | _, _ -> `List [`List unioned; `List simple]

  let of_json (json : json) : t =
    let (unioned, simple) =
    match json with
    | `List [`List unioned; `List simple] -> (unioned, simple)
    | `List ((`List _ :: _) as unioned) -> (unioned, [])
    | `List simple -> ([], simple)
    | _ -> raise (Error.Json "Invalid JSON for Effect.Type") in
    let unioned = List.map Id.of_json unioned in
    let simple = BnSet.of_list @@ List.map BoundName.of_json simple in
    { unioned_arg = None; unioned; simple; compound = IdSet.of_list unioned }
end

module Lift = struct
  type t =
    | Lift of SmartPrint.t * int
    | Mix of SmartPrint.t * int list
    | Inject of int

  let compute (d1 : Descriptor.t) (d2 : Descriptor.t)
    : bool list option * t option =
    let bs = Descriptor.subset_to_bools d1 d2 in
    if List.compare_lengths d1.unioned d2.unioned = 0 &&
        List.for_all2 (fun x y -> Descriptor.Id.compare x y = 0)
          d1.unioned d2.unioned then
      if d1.unioned = [] then
        (Some bs, None)
      else
        (Some (true :: bs), None)
    else
      match d1.unioned with
      | [] -> (Some (false :: bs), None)
      | (x :: xs) ->
        let bs = if List.mem false bs then Some (true :: bs) else None in
        match xs with
        | [] ->
          let in_list =
            to_coq_list (List.map (fun _ -> !^ "_") d2.unioned) in
          let n = find_index (fun y ->
            Descriptor.Id.compare x y = 0) d2.unioned in
          (bs, Some (Lift (in_list, n)))
        | _ ->
          match d2.unioned with
          | [] -> failwith "No backing union found."
          | [x] -> (bs, Some (Inject (List.length d1.unioned)))
          | _ ->
            let in_list =
              to_coq_list (List.map (fun _ -> !^ "_") d2.unioned) in
            let out_list = List.map (fun x ->
              find_index (fun y ->
                Descriptor.Id.compare x y = 0) d2.unioned) d1.unioned in
            (bs, Some (Mix (in_list, out_list)))
end

module Type = struct
  include Kerneltypes.Type
  type t = Descriptor.t Kerneltypes.Type.t'

  module Old = struct
    type t' =
      | Pure
      | Arrow of Descriptor.t * t'

    let to_type (typ : t') : t =
      let rec aux i typ =
        match typ with
        | Pure -> Kerneltypes.Type.Variable (string_of_int i ^ "A")
        | Arrow (d, typ) ->
          Kerneltypes.Type.Arrow (Kerneltypes.Type.Variable (string_of_int i ^ "A"),
            if Descriptor.is_pure d then
              aux (i+1) typ
            else
              Kerneltypes.Type.Monad (d, aux (i+1) typ)) in
      aux 1 typ

    let of_type (typ : t) : t' =
      let open Kerneltypes in
      let rec aux typ =
        match typ with
        | Kerneltypes.Type.Arrow (_, Kerneltypes.Type.Monad (d, typ)) ->
          Arrow (d, aux typ)
        | Kerneltypes.Type.Arrow (_, typ) -> Arrow (Descriptor.pure, aux typ)
        | Kerneltypes.Type.Monad (_, typ) -> aux typ
        | _ -> Pure in
      aux typ
  end

  let pure : t = Variable "_"
  let arrow (d : Descriptor.t) (typ : t) : t =
    if Descriptor.is_pure d then
      Arrow (pure, typ)
    else
      Arrow (pure, Monad (d, typ))

  let rec pp (typ : t) : SmartPrint.t =
    match typ with
    | Arrow (_, Monad (d, typ)) ->
      nest (!^ "." ^^ !^ "-" ^-^ Descriptor.pp d ^-^ !^ "->" ^^ pp typ)
    | Arrow (_, typ) ->
      nest (!^ "." ^^ !^ "->" ^^ pp typ)
    | Monad (_, typ) -> pp typ
    | _ -> !^ "."

  let rec is_pure (typ : t) : bool =
    match typ with
    | Monad (d, typ) -> Descriptor.is_pure d && is_pure typ
    | Arrow (_, typ) -> is_pure typ
    | _ -> true

  let rec compress (typ : t) : t = typ

  let rec map (f : BoundName.t -> BoundName.t) (typ : t) : t =
    match typ with
    | Monad (d, typ) -> Monad (Descriptor.map f d, map f typ)
    | Arrow (typ1, typ) -> Arrow (typ1, map f typ)
    | _ -> typ

  let rec return_descriptor (typ : t) (nb_args : int) : Descriptor.t =
    if nb_args = 0 then
      Descriptor.pure
    else
      match typ with
      | Arrow (_, Monad (d, typ)) ->
        Descriptor.union [d; return_descriptor typ (nb_args - 1)]
      | Arrow (_, typ) -> return_descriptor typ (nb_args - 1)
      | Monad (_, typ) -> return_descriptor typ nb_args
      | _ -> Descriptor.pure

  let rec return_type (typ : t) (nb_args : int) : t =
    if nb_args = 0 then
      typ
    else
      match typ with
      | Arrow (_, Monad (d, typ)) -> return_type typ (nb_args - 1)
      | Arrow (_, typ) -> return_type typ (nb_args - 1)
      | Monad (_, typ) -> return_type typ nb_args
      | _ -> typ

  let rec return_single_descriptor (typ : t) (nb_args : int) : Descriptor.t =
    if nb_args = 0 then
      Descriptor.pure
    else
      match typ with
      | Arrow (_, Monad (d, typ)) ->
        if nb_args = 1 then d
        else
          failwith "Found a non-pure callpoint earlier than expected."
      | Arrow (_, typ) -> return_single_descriptor typ (nb_args - 1)
      | Monad (_, typ) -> return_single_descriptor typ nb_args
      | _ -> Descriptor.pure

  let union (typs : t list) : t =
    let rec aux typ1 typ2 =
      match typ1, typ2 with
      | Arrow (typ1a, typ1b), Arrow (typ2a, typ2b) ->
        Arrow (typ1a, aux typ1b typ2b)
      | Monad (d1, typ1), Monad (d2, typ2) ->
        Monad (Descriptor.union [d1; d2], aux typ1 typ2)
      | Monad (d, typ1), typ2 | typ1, Monad (d, typ2) ->
        Monad (Descriptor.union [d], aux typ1 typ2)
      | _, _ -> typ1 in
    List.fold_left aux (Variable "_") typs

  let rec map_type_vars (vars_map : PureType.t Name.Map.t) (typ : t) : t =
    match typ with
    | Arrow (typ1, typ) ->
      Arrow (typ1, map_type_vars vars_map typ)
    | Monad (d, typ) ->
      Monad (Descriptor.map_type_vars vars_map d, map_type_vars vars_map typ)
    | _ -> typ

  let rec has_type_vars (typ : t) : bool =
    match typ with
    | Arrow (_, typ) -> has_type_vars typ
    | Monad (d, typ) -> Descriptor.has_type_vars d || has_type_vars typ
    | _ -> false

  let rec split_calls (typ : t) (e_xs : 'a list)
    : ('a list * Descriptor.t) list =
    match e_xs with
    | [] -> []
    | e_x :: e_xs ->
      let e_xs = split_calls (return_type typ 1) e_xs in
      let d = return_descriptor typ 1 in
      if Descriptor.is_pure d then
        match e_xs with
        | [] -> [([e_x], Descriptor.pure)]
        | (e_xs', d') :: e_xs -> ((e_x :: e_xs'), d') :: e_xs
      else
        ([e_x], d) :: e_xs

  let to_json (typ : t) : json =
    let rec to_json typ =
      match typ with
      | Arrow (_, Monad (d, typ)) -> Descriptor.to_json d :: to_json typ
      | Arrow (_, typ) -> Descriptor.to_json Descriptor.pure :: to_json typ
      | Monad (_, typ) -> to_json typ
      | _ -> [] in
    `List (to_json typ)

  let of_json (json : json) : t =
    let rec of_json l =
      match l with
      | [] -> Variable "_"
      | json :: l ->
        let d = Descriptor.of_json json in
        Arrow (Variable "_",
          if Descriptor.is_pure d then of_json l
          else Monad (d, of_json l)) in
    match json with
    | `List jsons -> of_json jsons
    | _ -> raise (Error.Json "List expected.")
end

type t = Descriptor.t Kerneltypes.Type.t'

type t' = { descriptor : Descriptor.t; typ : Type.t }

let to_type (e : t') : t =
  if Descriptor.is_pure e.descriptor then e.typ
  else Type.Monad (e.descriptor, e.typ)

let of_type (typ : t) : t' =
  match typ with
  | Type.Monad (d, typ) -> { descriptor = d; typ = typ }
  | _ -> { descriptor = Descriptor.pure; typ = typ }

let pp (effect : t) : SmartPrint.t =
  nest @@ !^ "Effect" ^^ OCaml.tuple @@
    match effect with
    | Type.Monad (d, typ) -> [Descriptor.pp d; Type.pp typ]
    | _ -> [Descriptor.pp Descriptor.pure; Type.pp effect]

let function_typ (args : 'a list) (body_effect : t) : t =
  match args with
  | [] -> body_effect
  | _ :: args ->
    args |> List.fold_left (fun effect_typ _ ->
        Type.Arrow (Type.pure, effect_typ))
      (Type.Arrow (Type.pure, body_effect))

let pure : t = Type.pure

let is_pure (effect : t) : bool = Type.is_pure effect

let eff (typ : Type.t) : t = typ

let union (effects : t list) : t = Type.union effects

let rec map (f : BoundName.t -> BoundName.t) (effect : t) : t =
  Type.map f effect

let map_type_vars (vars_map : PureType.t Name.Map.t) (effect : t) : t =
  Type.map_type_vars vars_map effect

let has_type_vars (effect : t) : bool = Type.has_type_vars effect

let compress (effect : t) : t = effect

let to_json (effect : t) : json =
  match effect with
  | Type.Monad (d, typ) ->
    `List [Descriptor.to_json d; Type.to_json typ]
  | _ ->
    if Type.is_pure effect then
      `List []
    else
      `List [Type.to_json effect]

let of_json (json : json) : t =
  match json with
  | `List [] -> Type.pure
  | `List [typ] -> Type.of_json typ
  | `List [d; typ] -> Type.Monad (Descriptor.of_json d, Type.of_json typ)
  | _ -> raise (Error.Json "List expected.")
