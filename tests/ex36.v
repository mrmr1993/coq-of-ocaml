Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Parameter op_eq_eq : bool -> bool -> bool.

Definition all_eqb (x : bool) (y : bool) (z : bool) : bool :=
  andb (op_eq_eq x y) (op_eq_eq y z).

Parameter op_eq : forall {a : Type}, a -> a -> bool.

Definition all_equal {A : Type} (x : A) (y : A) (z : A) : bool :=
  andb (op_eq x y) (op_eq y z).
