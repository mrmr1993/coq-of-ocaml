let is_some (x : 'a option) : bool =
  match x with | Some _ -> true | None -> false

let option_map (f : 'a -> 'b) (x : 'a option) : 'b option =
  match x with
  | Some x -> Some (f x)
  | None -> None

let rec option_filter (l : 'a option list) : 'a list =
  match l with
  | [] -> []
  | Some x :: l' -> x :: option_filter l'
  | None :: l' -> option_filter l'

let rec filter_map (f : 'a -> 'b option) (l : 'a list) : 'b list =
  match l with
  | [] -> []
  | a :: l' ->
    match f a with
    | Some b -> b :: filter_map f l'
    | None -> filter_map f l'

let rec mix_map2 (f : 'a -> bool) (g : 'a -> 'c) (h : 'a -> 'b -> 'c)
  (l1 : 'a list) (l2 : 'b list) : 'c list =
  match l1 with
  | [] -> []
  | a :: l1' ->
    if f a then
      match l2 with
      | [] -> []
      | b :: l2' -> h a b :: mix_map2 f g h l1' l2'
    else
      g a :: mix_map2 f g h l1' l2