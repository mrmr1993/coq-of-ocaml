(** Types for the effects. *)
open SmartPrint
open Yojson.Basic
open Utils

module Descriptor = struct
  type t = {
    args_arg : Name.t option;
    with_args : t CommonType.t list;
    no_args : t CommonType.t list;
  }

  type desc = t
  type typ = t CommonType.t

  module CommonTypeSet = Set.Make (struct
    type t = desc CommonType.t
    let compare x y = CommonType.compare x y
  end)

  let rec pp (d : t) : SmartPrint.t =
    OCaml.list (CommonType.pp pp) @@ d.with_args @ d.no_args

  let pure : t = {
    args_arg = None;
    with_args = [];
    no_args = [];
  }

  let is_pure (d : t) : bool =
    List.compare_length_with d.with_args 0 = 0 &&
    List.compare_length_with d.no_args 0 = 0

  let eq (d1 : t) (d2 : t) : bool =
    d1.with_args = d2.with_args && d1.no_args = d2.no_args

  let singleton (x : BoundName.t) (typs : typ list) : t =
    if typs = [] then {
        args_arg = None;
        with_args = [];
        no_args = [CommonType.Apply (x, [])];
      }
    else {
        args_arg = None;
        with_args =
          [CommonType.Apply (x, typs)];
        no_args = [];
      }

  let union (ds : t list) : t =
    let (compound, simple) = List.fold_left (fun (compound, simple) d ->
        (CommonTypeSet.union compound (CommonTypeSet.of_list d.with_args),
        CommonTypeSet.union simple (CommonTypeSet.of_list d.no_args)))
      (CommonTypeSet.empty, CommonTypeSet.empty) ds in
    {
      args_arg = None;
      with_args = CommonTypeSet.elements compound;
      no_args = CommonTypeSet.elements simple;
    }

  let remove (x : BoundName.t) (d : t) : t =
    { d with
      no_args = d.no_args |> List.filter (fun y ->
        compare y (CommonType.Apply (x, [])) <> 0)
    }

  let elements (d : t) : BoundName.t list =
    d.no_args |> List.map (fun typ ->
      match typ with
      | CommonType.Apply (name, []) -> name
      | _ -> failwith "Unexpected format of simple effect descriptor.")

  let index (x : BoundName.t) (d : t) : int =
    let rec find_index l f =
      match l with
      | [] -> 0
      | x :: xs -> if f x then 0 else 1 + find_index xs f in
    find_index d.no_args (fun y -> CommonType.Apply (x, []) = y)

  let set_unioned_arg (arg : Name.t) (d : t) : t =
    { d with args_arg = Some arg }

  let should_carry (d : t) : bool =
    List.compare_length_with d.with_args 2 >= 0

  let rec to_coq (d : t) : SmartPrint.t =
    let should_carry = should_carry d in
    let id_els =
      List.map (CommonType.to_coq to_coq should_carry) d.with_args in
    let id_els = if should_carry then
        [nest @@
          !^ "OCaml.Effect.Union.union" ^^
          (match d.args_arg with
           | Some arg -> Name.to_coq arg
           | None -> !^ "_") ^^
          OCaml.list (fun x -> x) id_els]
      else id_els in
    let bn_els = List.map (CommonType.to_coq to_coq should_carry) d.no_args in
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
    aux d1.no_args d2.no_args

  let map (f : BoundName.t -> BoundName.t) (d : t) : t =
    { d with
      with_args = List.map (CommonType.map f) d.with_args;
      no_args = List.map (CommonType.map f) d.no_args;
    }

  let map_type_vars (vars_map : typ Name.Map.t) (d : t) : t =
    { d with
      with_args = d.with_args |> List.map
        (CommonType.map_vars (fun x -> Name.Map.find x vars_map));
      no_args = d.no_args |> List.map
        (CommonType.map_vars (fun x -> Name.Map.find x vars_map));
    }

  let rec to_json (d : t) : json =
    let unioned = List.map (CommonType.to_json to_json) d.with_args in
    let simple = d.no_args |> List.map (fun typ ->
      match typ with
      | CommonType.Apply (name, []) -> BoundName.to_json name
      | _ -> failwith "Unexpected format of simple effect descriptor.") in
    match unioned, simple with
    | [], [] -> `List []
    | [], _ -> `List simple
    | _, [] -> `List unioned
    | _, _ -> `List [`List unioned; `List simple]

  let rec of_json (json : json) : t =
    let (unioned, simple) =
    match json with
    | `List [`List unioned; `List simple] -> (unioned, simple)
    | `List ((`List _ :: _) as unioned) -> (unioned, [])
    | `List simple -> ([], simple)
    | _ -> raise (Error.Json "Invalid JSON for Effect.Type") in
    let unioned = List.map (CommonType.of_json of_json) unioned in
    let simple = simple |> List.map (fun json ->
      CommonType.Apply (BoundName.of_json json, [])) in
    { args_arg = None; with_args = unioned; no_args = simple }
end

module Lift = struct
  type t =
    | Lift of SmartPrint.t * int
    | Mix of SmartPrint.t * int list
    | Inject of int

  let compute (d1 : Descriptor.t) (d2 : Descriptor.t)
    : bool list option * t option =
    let bs = Descriptor.subset_to_bools d1 d2 in
    if List.compare_lengths d1.with_args d2.with_args = 0 &&
        List.for_all2 (fun x y -> CommonType.compare x y = 0)
          d1.with_args d2.with_args then
      if d1.with_args = [] then
        (Some bs, None)
      else
        (Some (true :: bs), None)
    else
      match d1.with_args with
      | [] -> (Some (false :: bs), None)
      | (x :: xs) ->
        let bs = if List.mem false bs then Some (true :: bs) else None in
        match xs with
        | [] ->
          let in_list =
            to_coq_list (List.map (fun _ -> !^ "_") d2.with_args) in
          let n = find_index (fun y ->
            CommonType.compare x y = 0) d2.with_args in
          (bs, Some (Lift (in_list, n)))
        | _ ->
          match d2.with_args with
          | [] -> failwith "No backing union found."
          | [x] -> (bs, Some (Inject (List.length d1.with_args)))
          | _ ->
            let in_list =
              to_coq_list (List.map (fun _ -> !^ "_") d2.with_args) in
            let out_list = List.map (fun x ->
              find_index (fun y ->
                CommonType.compare x y = 0) d2.with_args) d1.with_args in
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

  let unify ?collapse:(collapse=true) (typ1 : t) (typ2 : t) : t =
    let f = if collapse then
        (fun d1 d2 ->
          Descriptor.union @@ match d2 with
          | Some d2 -> [d1; d2]
          | None -> [d1])
      else
        (fun d1 d2 ->
          match d2 with
          | Some d2 -> Descriptor.union [d1; d2]
          | None -> d1) in
    CommonType.unify_monad f typ1 typ2

  let union (typs : t list) : t =
    List.fold_left unify pure typs

  let rec map_type_vars (vars_map : t Name.Map.t) (typ : t) : t =
    match typ with
    | Arrow (typ1, typ) ->
      Arrow (typ1, map_type_vars vars_map typ)
    | Monad (d, typ) ->
      Monad (Descriptor.map_type_vars vars_map d, map_type_vars vars_map typ)
    | _ -> typ

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

let join (d : Descriptor.t) (typ : Type.t) =
  if Descriptor.is_pure d then typ
  else Type.Monad (d, typ)

let split (effect : t) : Descriptor.t * t =
  match effect with
  | Type.Monad (d, typ) -> (d, typ)
  | _ -> (Descriptor.pure, effect)

let pp (effect : t) : SmartPrint.t =
  nest @@ !^ "Effect" ^^ OCaml.tuple @@
    match effect with
    | Type.Monad (d, typ) -> [Descriptor.pp d; Type.pp typ]
    | _ -> [Descriptor.pp Descriptor.pure; Type.pp effect]

let function_typ (args : ('a * t) list) (body_effect : t) : t =
  List.fold_right (fun (_, typ) effect_typ -> Type.Arrow (typ, effect_typ))
    args body_effect

let pure : t = Type.pure

let is_pure (effect : t) : bool = Type.is_pure effect

let eff (typ : Type.t) : t = typ

let union (effects : t list) : t = Type.union effects

let rec map (f : BoundName.t -> BoundName.t) (effect : t) : t =
  Type.map f effect

let map_type_vars (vars_map : t Name.Map.t) (effect : t) : t =
  Type.map_type_vars vars_map effect

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
