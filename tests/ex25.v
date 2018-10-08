Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Require OCaml.List.

Definition l1 : list Z := [].

Definition l2 : list Z := cons 1 (cons 2 (cons 3 (cons 4 []))).

Definition l3 : list (Z * string) :=
  cons (1, "one" % string) (cons (2, "two" % string) []).

Definition s1 : Z := OCaml.List.length l1.

Definition s2 : Z := OCaml.List.length l2.

Definition h {A : Type} (x : A) : M [ OCaml.exception OCaml.failure ] Z :=
  match x with
  | _ => OCaml.List.hd l2
  end.

Definition t {A : Type} (x : A)
  : M [ OCaml.exception OCaml.failure ] (list Z) :=
  match x with
  | _ => OCaml.List.tl l2
  end.

Definition x {A : Type} (x : A)
  : M [ OCaml.exception OCaml.failure; OCaml.exception OCaml.invalid_argument ]
    Z :=
  match x with
  | _ => OCaml.List.nth l2 1
  end.

Definition rl : list Z := OCaml.List.rev l2.

Definition ll : list Z := OCaml.List.append l2 l2.

Definition rll : list Z := OCaml.List.rev_append l2 l2.

Definition lc : list Z :=
  OCaml.List.concat (cons l1 (cons l2 (cons l1 (cons l2 [])))).

Definition lf : list Z :=
  OCaml.List.flatten (cons l1 (cons l2 (cons l1 (cons l2 [])))).

Definition m : list Z := OCaml.List.map (fun x => Z.add x 1) l2.

Definition mi : list Z := OCaml.List.mapi (fun i => fun x => Z.add x i) l2.

Definition rm : list Z := OCaml.List.rev_map (fun x => Z.add x 1) l2.

Definition fl : Z := OCaml.List.fold_left (fun s => fun x => Z.add s x) 0 l2.

Definition fr : Z := OCaml.List.fold_right (fun x => fun s => Z.add s x) l2 0.

Definition m2 {A : Type} (x_1 : A)
  : M [ OCaml.exception OCaml.invalid_argument ] (list Z) :=
  match x_1 with
  | _ => OCaml.List.map2 (fun x => fun y => Z.add x y) l2 l2
  end.

Definition rm2 {A : Type} (x_1 : A)
  : M [ OCaml.exception OCaml.invalid_argument ] (list Z) :=
  match x_1 with
  | _ => OCaml.List.rev_map2 (fun x => fun y => Z.add x y) l2 l2
  end.

Definition fl2 {A : Type} (x_1 : A)
  : M [ OCaml.exception OCaml.invalid_argument ] Z :=
  match x_1 with
  | _ =>
    OCaml.List.fold_left2 (fun s => fun x => fun y => Z.add (Z.add s x) y) 0 l2
      l2
  end.

Definition fr2 {A : Type} (x_1 : A)
  : M [ OCaml.exception OCaml.invalid_argument ] Z :=
  match x_1 with
  | _ =>
    OCaml.List.fold_right2 (fun s => fun x => fun y => Z.add (Z.add s x) y) l2
      l2 0
  end.

Definition all : bool := OCaml.List.for_all (fun x => equiv_decb x 2) l2.

Definition ex : bool := OCaml.List._exists (fun x => equiv_decb x 2) l2.

Definition all2 {A : Type} (x_1 : A)
  : M [ OCaml.exception OCaml.invalid_argument ] bool :=
  match x_1 with
  | _ => OCaml.List.for_all2 (fun x => fun y => equiv_decb x y) l2 l2
  end.

Definition ex2 {A : Type} (x_1 : A)
  : M [ OCaml.exception OCaml.invalid_argument ] bool :=
  match x_1 with
  | _ => OCaml.List._exists2 (fun x => fun y => equiv_decb x y) l2 l2
  end.

Definition me : bool := OCaml.List.mem 2 l2.

Definition fin {A : Type} (x_1 : A) : M [ OCaml.exception OCaml.not_found ] Z :=
  match x_1 with
  | _ => OCaml.List.find (fun x => equiv_decb x 1) l2
  end.

Definition fil : list Z :=
  OCaml.List.filter (fun x => OCaml.Pervasives.ge x 2) l2.

Definition fina : list Z :=
  OCaml.List.find_all (fun x => OCaml.Pervasives.ge x 2) l2.

Definition par : (list Z) * (list Z) :=
  OCaml.List.partition (fun x => OCaml.Pervasives.gt x 2) l2.

Definition asso {A : Type} (x_1 : A)
  : M [ OCaml.exception OCaml.not_found ] string :=
  match x_1 with
  | _ => OCaml.List.assoc 2 l3
  end.

Definition masso {A : Type} (x_1 : A) : bool :=
  match x_1 with
  | _ => OCaml.List.mem_assoc 2 l3
  end.

Definition rasso {A : Type} (x_1 : A) : list (Z * string) :=
  match x_1 with
  | _ => OCaml.List.remove_assoc 2 l3
  end.

Definition sp : (list Z) * (list string) := OCaml.List.split l3.

Definition com {A : Type} (x_1 : A)
  : M [ OCaml.exception OCaml.invalid_argument ] (list (Z * Z)) :=
  match x_1 with
  | _ => OCaml.List.combine l2 l2
  end.

Definition so {A : Type} (x_1 : A) : M [ Counter; NonTermination ] (list Z) :=
  match x_1 with
  | _ => OCaml.List.sort (fun x => fun y => Z.sub y x) l2
  end.

Definition sso {A : Type} (x_1 : A) : M [ Counter; NonTermination ] (list Z) :=
  match x_1 with
  | _ => OCaml.List.stable_sort (fun x => fun y => Z.sub y x) l2
  end.

Definition fso {A : Type} (x_1 : A) : M [ Counter; NonTermination ] (list Z) :=
  match x_1 with
  | _ => OCaml.List.fast_sort (fun x => fun y => Z.sub y x) l2
  end.

Definition mer : list Z :=
  OCaml.List.merge (fun x => fun y => Z.sub y x) l2
    (cons 2 (cons (-1) (cons 5 []))).
