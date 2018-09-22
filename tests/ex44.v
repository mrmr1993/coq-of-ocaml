Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition temp : unit := OCaml.Pervasives.ignore (Z.add 1 1).

Definition temp_1 : Z * string := (15, "hi" % string).

Definition a : Z :=
  match temp_1 with
  | (a, b) => a
  end.

Definition b : string :=
  match temp_1 with
  | (a, b) => b
  end.

Inductive a_1 : Type :=
| A : Z -> bool -> a_1.

Definition temp_2 : a_1 := A 15 true.

Definition i : Z :=
  match temp_2 with
  | A i j => i
  end.

Definition j : bool :=
  match temp_2 with
  | A i j => j
  end.

Record b_1 : Type := {
  first : Z;
  second : bool;
  third : string }.

Definition b_val : b_1 :=
  {| first := 12; second := false; third := "hello" % string |}.

Definition hi : Z :=
  match b_val with
  | {| first := hi |} => hi
  end.

Definition hey : bool :=
  match b_val with
  | {| second := hey |} => hey
  end.

Definition temp_5 : b_1 := b_val.

Definition hello : string :=
  match temp_5 with
  | {| second := hey_1; third := hello |} => hello
  end.

Definition hey_1 : bool :=
  match temp_5 with
  | {| second := hey_1; third := hello |} => hey_1
  end.

Definition temp_6 : b_1 := {| first := hi; second := hey_1; third := hello |}.

Definition first_1 : Z :=
  match temp_6 with
  | {| first := first_1; second := second_1; third := third_1 |} => first_1
  end.

Definition second_1 : bool :=
  match temp_6 with
  | {| first := first_1; second := second_1; third := third_1 |} => second_1
  end.

Definition third_1 : string :=
  match temp_6 with
  | {| first := first_1; second := second_1; third := third_1 |} => third_1
  end.
