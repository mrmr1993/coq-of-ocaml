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

let rec find_first (f : 'a -> 'b option) (l : 'a list) : 'b option =
  match l with
  | [] -> None
  | x :: l ->
    (match f x with
    | None -> find_first f l
    | y -> y)

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

let find_index (f : 'a -> bool) (l : 'a list) : int =
  let rec aux l c =
    match l with
    | [] -> failwith "Not found."
    | x :: l -> if f x then c else aux l (c+1) in
  aux l 0

let to_coq_list (l : SmartPrint.t list) : SmartPrint.t =
  let open SmartPrint in
  brakets @@ separate (!^ ";") l

let rec strip_prefix (l_prefix : 'a list) (l : 'a list) : 'a list option =
  match l_prefix, l with
  | [], l -> Some l
  | a :: l_prefix, b :: l when a = b -> strip_prefix l_prefix l
  | _, _ -> None

let rec drop (n : int) (l : 'a list) : 'a list =
  if n <= 0 then l
  else
    match l with
    | [] -> l
    | a :: l -> drop (n-1) l

let rec take (n : int) (l : 'a list) : 'a list =
  if n <= 0 then []
  else
    match l with
    | [] -> []
    | a :: l -> a :: take (n-1) l

let rec map_with_acc (f : 'a -> 'b -> 'a * 'c) (a : 'a) (l : 'b list)
  : 'c list =
  match l with
  | [] -> []
  | x :: l ->
    let (a, x) = f a x in
    x :: map_with_acc f a l

let rec compare_list (compare : 'a -> 'a -> int) (l1 : 'a list) (l2 : 'a list)
  : int =
  match l1, l2 with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | a :: l1, b :: l2 ->
    let cmp = compare a b in
    if cmp = 0 then compare_list compare l1 l2 else cmp
