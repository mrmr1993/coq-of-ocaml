Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition temp : unit := OCaml.Pervasives.ignore (Z.add 1 1).

Definition temp_1 : Z * string := (15, "hi" % string).

Definition a : _ :=
  match temp_1 with
  | (a, b) => a
  end.

Definition b : _ :=
  match temp_1 with
  | (a, b) => b
  end.

Inductive a_1 : Type :=
| A : Z -> bool -> a_1.

Definition temp_2 : a_1 := A 15 true.

Definition i : _ :=
  match temp_2 with
  | A i j => i
  end.

Definition j : _ :=
  match temp_2 with
  | A i j => j
  end.
