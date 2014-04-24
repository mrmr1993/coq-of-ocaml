open SmartPrint

type t =
  | None
  | CoqRec
  | FreeRec

let pp (attr : t) : SmartPrint.t =
  match attr with
  | None -> !^ "@."
  | CoqRec -> !^ "@coq_rec"
  | FreeRec -> !^ "@free_rec"

let warn_incompatible_attributes (loc : Loc.t) : unit =
  Error.warn loc "There cannot be both \"@coq_rec\" and \"@free_rec\" attributes."

let of_attributes (loc : Loc.t) (attrs : Typedtree.attributes) : t =
  let attrs : string list = List.map (fun attr -> (fst attr).Asttypes.txt) attrs in
  if List.mem "coq_rec" attrs && List.mem "free_rec" attrs then
    warn_incompatible_attributes loc;
  if List.mem "coq_rec" attrs then
    CoqRec
  else if List.mem "free_rec" attrs then
    FreeRec
  else
    None

let combine (loc : Loc.t) (attr1 : t) (attr2 : t) : t =
  match (attr1, attr2) with
  | (None, _) -> attr2
  | (_, None) -> attr1
  | (CoqRec, CoqRec) -> CoqRec
  | (FreeRec, FreeRec) -> FreeRec
  | (CoqRec, FreeRec) | (FreeRec, CoqRec) ->
    warn_incompatible_attributes loc;
    CoqRec