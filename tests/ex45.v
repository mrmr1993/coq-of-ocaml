Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition Ex1 := Effect.make unit unit.

Definition raise_Ex1 {A : Type} (x : unit) : M [ Ex1 ] A :=
  fun s => (inr (inl x), s).

Definition Ex2 := Effect.make unit (Z).

Definition raise_Ex2 {A : Type} (x : Z) : M [ Ex2 ] A :=
  fun s => (inr (inl x), s).

Definition f {A : Type} (x : unit) : M [ Ex1 ] A :=
  match x with
  | tt => raise_Ex1 tt
  end.

Definition g {A : Type} (y : Z) : M [ Ex2 ] A := raise_Ex2 (y).

Definition h {A : Type} (x : unit) : Z -> unit -> M [ Ex2 ] A :=
  match x with
  | tt =>
    fun y =>
      fun x_1 =>
        match x_1 with
        | tt => raise_Ex2 (y)
        end
  end.

Definition x {A B C : Type}
  : (unit -> M [ Ex1 ] A) * (Z -> M [ Ex2 ] B) *
    (unit -> Z -> unit -> M [ Ex2 ] C) := (f, g, h).

Definition f' {A : Type} : unit -> M [ Ex1 ] A :=
  match
    x :
      (unit -> M [ Ex1 ] A) * (Z -> M [ Ex2 ] unit) *
        (unit -> Z -> unit -> M [ Ex2 ] unit) with
  | (f, _, _) => f
  end.

Definition g' {A : Type} : Z -> M [ Ex2 ] A :=
  match
    x :
      (unit -> M [ Ex1 ] unit) * (Z -> M [ Ex2 ] A) *
        (unit -> Z -> unit -> M [ Ex2 ] unit) with
  | (_, g, _) => g
  end.

Definition h' {A : Type} : unit -> Z -> unit -> M [ Ex2 ] A :=
  match
    x :
      (unit -> M [ Ex1 ] unit) * (Z -> M [ Ex2 ] unit) *
        (unit -> Z -> unit -> M [ Ex2 ] A) with
  | (_, _, h) => h
  end.

Definition temp {A B C : Type}
  : (unit -> M [ Ex1 ] A) * (Z -> M [ Ex2 ] B) *
    (unit -> Z -> unit -> M [ Ex2 ] C) := x.

Definition f'' {A : Type} : unit -> M [ Ex1 ] A :=
  match
    temp :
      (unit -> M [ Ex1 ] A) * (Z -> M [ Ex2 ] unit) *
        (unit -> Z -> unit -> M [ Ex2 ] unit) with
  | (f'', g'', h'') => f''
  end.

Definition g'' {B : Type} : Z -> M [ Ex2 ] B :=
  match
    temp :
      (unit -> M [ Ex1 ] unit) * (Z -> M [ Ex2 ] B) *
        (unit -> Z -> unit -> M [ Ex2 ] unit) with
  | (f'', g'', h'') => g''
  end.

Definition h'' {C : Type} : unit -> Z -> unit -> M [ Ex2 ] C :=
  match
    temp :
      (unit -> M [ Ex1 ] unit) * (Z -> M [ Ex2 ] unit) *
        (unit -> Z -> unit -> M [ Ex2 ] C) with
  | (f'', g'', h'') => h''
  end.

Definition ff {A : Type} : unit -> M [ Ex1 ] A :=
  match
    x :
      (unit -> M [ Ex1 ] A) * (Z -> M [ Ex2 ] unit) *
        (unit -> Z -> unit -> M [ Ex2 ] unit) with
  | (f, _, _) => f
  end.

Definition gg {A : Type} : Z -> M [ Ex2 ] A :=
  match
    x :
      (unit -> M [ Ex1 ] unit) * (Z -> M [ Ex2 ] A) *
        (unit -> Z -> unit -> M [ Ex2 ] unit) with
  | (_, g, _) => g
  end.

Definition hh {A : Type} : unit -> Z -> unit -> M [ Ex2 ] A :=
  match
    x :
      (unit -> M [ Ex1 ] unit) * (Z -> M [ Ex2 ] unit) *
        (unit -> Z -> unit -> M [ Ex2 ] A) with
  | (_, _, h) => h
  end.

Definition fff : unit -> M [ Ex1 ] unit :=
  match
    x :
      (unit -> M [ Ex1 ] unit) * (Z -> M [ Ex2 ] unit) *
        (unit -> Z -> unit -> M [ Ex2 ] unit) with
  | (f, _, _) => f
  end.

Definition ggg : Z -> M [ Ex2 ] unit :=
  match
    x :
      (unit -> M [ Ex1 ] unit) * (Z -> M [ Ex2 ] unit) *
        (unit -> Z -> unit -> M [ Ex2 ] unit) with
  | (_, g, _) => g
  end.

Definition hhh : unit -> Z -> unit -> M [ Ex2 ] unit :=
  match
    x :
      (unit -> M [ Ex1 ] unit) * (Z -> M [ Ex2 ] unit) *
        (unit -> Z -> unit -> M [ Ex2 ] unit) with
  | (_, _, h) => h
  end.

Definition f1 {A : Type} : unit -> M [ Ex1 ] A :=
  match f : unit -> M [ Ex1 ] A with
  | x => x
  end.

Definition g1 {A : Type} : Z -> M [ Ex2 ] A :=
  match g : Z -> M [ Ex2 ] A with
  | x => x
  end.

Definition h1 {A : Type} : unit -> Z -> unit -> M [ Ex2 ] A :=
  match h : unit -> Z -> unit -> M [ Ex2 ] A with
  | x => x
  end.
