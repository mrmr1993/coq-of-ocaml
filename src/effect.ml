(** Types for the effects. *)
open SmartPrint
open Yojson.Basic
open Utils

module Descriptor = struct
  include CommonType.Type
  type t = desc

  let rec pp (d : t) : SmartPrint.t = CommonType.pp_desc d

  let pure : t = {
    args_arg = None;
    with_args = [];
    no_args = [];
  }

  let is_pure (d : t) : bool =
    List.compare_length_with d.with_args 0 = 0 &&
    List.compare_length_with d.no_args 0 = 0

  let eq (d1 : t) (d2 : t) : bool = CommonType.compare_desc d1 d2 = 0

  let singleton ?simple:(simple=false) (x : BoundName.t) (typs : typ list) : t =
    if typs = [] || simple then {
        args_arg = None;
        with_args = [];
        no_args = [CommonType.Apply (x, typs)];
      }
    else {
        args_arg = None;
        with_args =
          [CommonType.Apply (x, typs)];
        no_args = [];
      }

  let union (ds : t list) : t =
    let (compound, simple) = List.fold_left (fun (compound, simple) d ->
        (CommonType.Set.union compound (CommonType.Set.of_list d.with_args),
        CommonType.Set.union simple (CommonType.Set.of_list d.no_args)))
      (CommonType.Set.empty, CommonType.Set.empty) ds in
    {
      args_arg = None;
      with_args = CommonType.Set.elements compound;
      no_args = CommonType.Set.elements simple;
    }

  let remove (x : CommonType.t) (d : t) : t =
    { d with
      no_args = d.no_args |> List.filter (fun y -> CommonType.compare x y <> 0)
    }

  let find_candidate (f : CommonType.t -> CommonType.t -> CommonType.t option)
    (x : CommonType.t) (d : t) : CommonType.t =
    let rec find_candidate dl =
      match dl with
      | [] -> failwith "Could not find a candidate descriptor."
      | d :: dl ->
        match f d x with
        | Some d -> d
        | None -> find_candidate dl in
    find_candidate d.no_args

  let elements (d : t) : BoundName.t list =
    d.no_args |> List.map (fun typ ->
      match typ with
      | CommonType.Apply (name, []) -> name
      | _ -> failwith "Unexpected format of simple effect descriptor.")

  let index (x : CommonType.t) (d : t) : int =
    let rec find_index l f =
      match l with
      | [] -> 0
      | x :: xs -> if f x then 0 else 1 + find_index xs f in
    find_index d.no_args (fun y -> CommonType.compare x y = 0) +
      match d.with_args with
      | [] -> 0
      | _ -> 1

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
        if CommonType.compare x1 x2 = 0 then
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
    CommonType.map_desc_vars (fun x -> Name.Map.find x vars_map) d

  let to_json (d : t) : json = CommonType.desc_to_json d

  let of_json (json : json) : t = CommonType.desc_of_json json
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
  include CommonType.Type
  type t = typ

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

type t = CommonType.typ

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
