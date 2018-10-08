Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Inductive ex1 : Type :=
| Ex1 : unit -> ex1.

Inductive ex2 : Type :=
| Ex2 : (Z) -> ex2.

Definition f {A : Type} (x : unit) : M [ OCaml.exception ex1 ] A :=
  match x with
  | tt => Pervasives.raise (Ex1 tt)
  end.

Definition g {A : Type} (y : Z) : M [ OCaml.exception ex2 ] A :=
  Pervasives.raise (Ex2 (y)).

Definition h {A : Type} (x : unit) : Z -> unit -> M [ OCaml.exception ex2 ] A :=
  match x with
  | tt =>
    fun y =>
      fun x_1 =>
        match x_1 with
        | tt => Pervasives.raise (Ex2 (y))
        end
  end.

Definition x {A B C : Type}
  : (unit -> M [ OCaml.exception ex1 ] A) * (Z -> M [ OCaml.exception ex2 ] B) *
    (unit -> Z -> unit -> M [ OCaml.exception ex2 ] C) := (f, g, h).

Definition f' {A : Type} : unit -> M [ OCaml.exception ex1 ] A :=
  match
    x :
      (unit -> M [ OCaml.exception ex1 ] A) *
        (Z -> M [ OCaml.exception ex2 ] unit) *
        (unit -> Z -> unit -> M [ OCaml.exception ex2 ] unit) with
  | (f, _, _) => f
  end.

Definition g' {A : Type} : Z -> M [ OCaml.exception ex2 ] A :=
  match
    x :
      (unit -> M [ OCaml.exception ex1 ] unit) *
        (Z -> M [ OCaml.exception ex2 ] A) *
        (unit -> Z -> unit -> M [ OCaml.exception ex2 ] unit) with
  | (_, g, _) => g
  end.

Definition h' {A : Type} : unit -> Z -> unit -> M [ OCaml.exception ex2 ] A :=
  match
    x :
      (unit -> M [ OCaml.exception ex1 ] unit) *
        (Z -> M [ OCaml.exception ex2 ] unit) *
        (unit -> Z -> unit -> M [ OCaml.exception ex2 ] A) with
  | (_, _, h) => h
  end.

Definition temp {A B C : Type}
  : (unit -> M [ OCaml.exception ex1 ] A) * (Z -> M [ OCaml.exception ex2 ] B) *
    (unit -> Z -> unit -> M [ OCaml.exception ex2 ] C) := x.

Definition f'' {A : Type} : unit -> M [ OCaml.exception ex1 ] A :=
  match
    temp :
      (unit -> M [ OCaml.exception ex1 ] A) *
        (Z -> M [ OCaml.exception ex2 ] unit) *
        (unit -> Z -> unit -> M [ OCaml.exception ex2 ] unit) with
  | (f'', g'', h'') => f''
  end.

Definition g'' {B : Type} : Z -> M [ OCaml.exception ex2 ] B :=
  match
    temp :
      (unit -> M [ OCaml.exception ex1 ] unit) *
        (Z -> M [ OCaml.exception ex2 ] B) *
        (unit -> Z -> unit -> M [ OCaml.exception ex2 ] unit) with
  | (f'', g'', h'') => g''
  end.

Definition h'' {C : Type} : unit -> Z -> unit -> M [ OCaml.exception ex2 ] C :=
  match
    temp :
      (unit -> M [ OCaml.exception ex1 ] unit) *
        (Z -> M [ OCaml.exception ex2 ] unit) *
        (unit -> Z -> unit -> M [ OCaml.exception ex2 ] C) with
  | (f'', g'', h'') => h''
  end.

Definition ff {A : Type} : unit -> M [ OCaml.exception ex1 ] A :=
  match
    x :
      (unit -> M [ OCaml.exception ex1 ] A) *
        (Z -> M [ OCaml.exception ex2 ] unit) *
        (unit -> Z -> unit -> M [ OCaml.exception ex2 ] unit) with
  | (f, _, _) => f
  end.

Definition gg {A : Type} : Z -> M [ OCaml.exception ex2 ] A :=
  match
    x :
      (unit -> M [ OCaml.exception ex1 ] unit) *
        (Z -> M [ OCaml.exception ex2 ] A) *
        (unit -> Z -> unit -> M [ OCaml.exception ex2 ] unit) with
  | (_, g, _) => g
  end.

Definition hh {A : Type} : unit -> Z -> unit -> M [ OCaml.exception ex2 ] A :=
  match
    x :
      (unit -> M [ OCaml.exception ex1 ] unit) *
        (Z -> M [ OCaml.exception ex2 ] unit) *
        (unit -> Z -> unit -> M [ OCaml.exception ex2 ] A) with
  | (_, _, h) => h
  end.

Definition fff : unit -> M [ OCaml.exception ex1 ] unit :=
  match
    x :
      (unit -> M [ OCaml.exception ex1 ] unit) *
        (Z -> M [ OCaml.exception ex2 ] unit) *
        (unit -> Z -> unit -> M [ OCaml.exception ex2 ] unit) with
  | (f, _, _) => f
  end.

Definition ggg : Z -> M [ OCaml.exception ex2 ] unit :=
  match
    x :
      (unit -> M [ OCaml.exception ex1 ] unit) *
        (Z -> M [ OCaml.exception ex2 ] unit) *
        (unit -> Z -> unit -> M [ OCaml.exception ex2 ] unit) with
  | (_, g, _) => g
  end.

Definition hhh : unit -> Z -> unit -> M [ OCaml.exception ex2 ] unit :=
  match
    x :
      (unit -> M [ OCaml.exception ex1 ] unit) *
        (Z -> M [ OCaml.exception ex2 ] unit) *
        (unit -> Z -> unit -> M [ OCaml.exception ex2 ] unit) with
  | (_, _, h) => h
  end.

Definition f1 {A : Type} : unit -> M [ OCaml.exception ex1 ] A :=
  match f : unit -> M [ OCaml.exception ex1 ] A with
  | x => x
  end.

Definition g1 {A : Type} : Z -> M [ OCaml.exception ex2 ] A :=
  match g : Z -> M [ OCaml.exception ex2 ] A with
  | x => x
  end.

Definition h1 {A : Type} : unit -> Z -> unit -> M [ OCaml.exception ex2 ] A :=
  match h : unit -> Z -> unit -> M [ OCaml.exception ex2 ] A with
  | x => x
  end.
