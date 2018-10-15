Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Require OCaml.List.

Definition l1 : list Z := [].

Definition l2 : list Z := cons 1 (cons 2 (cons 3 (cons 4 []))).

Definition l3 : list (Z * string) :=
  cons (1, "one" % string) (cons (2, "two" % string) []).

Definition s1 : Z := List.length l1.

Definition s2 : Z := List.length l2.

Definition h {A : Type} (x : A) : M [ exception failure ] Z :=
  match x with
  | _ => List.hd l2
  end.

Definition t {A : Type} (x : A) : M [ exception failure ] (list Z) :=
  match x with
  | _ => List.tl l2
  end.

Definition x {A : Type} (x : A)
  : M [ exception failure; exception invalid_argument ] Z :=
  match x with
  | _ => List.nth l2 1
  end.

Definition rl : list Z := List.rev l2.

Definition ll : list Z := List.append l2 l2.

Definition rll : list Z := List.rev_append l2 l2.

Definition lc : list Z :=
  List.concat (cons l1 (cons l2 (cons l1 (cons l2 [])))).

Definition lf : list Z :=
  List.flatten (cons l1 (cons l2 (cons l1 (cons l2 [])))).

Definition m : list Z := List.map (fun x => Z.add x 1) l2.

Definition mi : list Z := List.mapi (fun i => fun x => Z.add x i) l2.

Definition rm : list Z := List.rev_map (fun x => Z.add x 1) l2.

Definition fl : Z := List.fold_left (fun s => fun x => Z.add s x) 0 l2.

Definition fr : Z := List.fold_right (fun x => fun s => Z.add s x) l2 0.

Definition m2 {A : Type} (x_1 : A)
  : M [ exception invalid_argument ] (list Z) :=
  match x_1 with
  | _ => List.map2 (fun x => fun y => Z.add x y) l2 l2
  end.

Definition rm2 {A : Type} (x_1 : A)
  : M [ exception invalid_argument ] (list Z) :=
  match x_1 with
  | _ => List.rev_map2 (fun x => fun y => Z.add x y) l2 l2
  end.

Definition fl2 {A : Type} (x_1 : A) : M [ exception invalid_argument ] Z :=
  match x_1 with
  | _ =>
    List.fold_left2 (fun s => fun x => fun y => Z.add (Z.add s x) y) 0 l2 l2
  end.

Definition fr2 {A : Type} (x_1 : A) : M [ exception invalid_argument ] Z :=
  match x_1 with
  | _ =>
    List.fold_right2 (fun s => fun x => fun y => Z.add (Z.add s x) y) l2 l2 0
  end.

Definition all : bool := List.for_all (fun x => equiv_decb x 2) l2.

Definition ex : bool := List._exists (fun x => equiv_decb x 2) l2.

Definition all2 {A : Type} (x_1 : A) : M [ exception invalid_argument ] bool :=
  match x_1 with
  | _ => List.for_all2 (fun x => fun y => equiv_decb x y) l2 l2
  end.

Definition ex2 {A : Type} (x_1 : A) : M [ exception invalid_argument ] bool :=
  match x_1 with
  | _ => List._exists2 (fun x => fun y => equiv_decb x y) l2 l2
  end.

Definition me : bool := List.mem 2 l2.

Definition fin {A : Type} (x_1 : A) : M [ exception not_found ] Z :=
  match x_1 with
  | _ => List.find (fun x => equiv_decb x 1) l2
  end.

Definition fil : list Z := List.filter (fun x => Pervasives.ge x 2) l2.

Definition fina : list Z := List.find_all (fun x => Pervasives.ge x 2) l2.

Definition par : (list Z) * (list Z) :=
  List.partition (fun x => Pervasives.gt x 2) l2.

Definition asso {A : Type} (x_1 : A) : M [ exception not_found ] string :=
  match x_1 with
  | _ => List.assoc 2 l3
  end.

Definition masso {A : Type} (x_1 : A) : bool :=
  match x_1 with
  | _ => List.mem_assoc 2 l3
  end.

Definition rasso {A : Type} (x_1 : A) : list (Z * string) :=
  match x_1 with
  | _ => List.remove_assoc 2 l3
  end.

Definition sp : (list Z) * (list string) := List.split l3.

Definition com {A : Type} (x_1 : A)
  : M [ exception invalid_argument ] (list (Z * Z)) :=
  match x_1 with
  | _ => List.combine l2 l2
  end.

Definition so {A : Type} (x_1 : A) : M [ Counter; NonTermination ] (list Z) :=
  match x_1 with
  | _ => List.sort (fun x => fun y => Z.sub y x) l2
  end.

Definition sso {A : Type} (x_1 : A) : M [ Counter; NonTermination ] (list Z) :=
  match x_1 with
  | _ => List.stable_sort (fun x => fun y => Z.sub y x) l2
  end.

Definition fso {A : Type} (x_1 : A) : M [ Counter; NonTermination ] (list Z) :=
  match x_1 with
  | _ => List.fast_sort (fun x => fun y => Z.sub y x) l2
  end.

Definition mer : list Z :=
  List.merge (fun x => fun y => Z.sub y x) l2 (cons 2 (cons (-1) (cons 5 []))).
