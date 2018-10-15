Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition a_state := OCaml.Effect.State.global_state.
Definition a : M [ OCaml.Effect.State.state Z; a_state ]
  (OCaml.Effect.State.t Z) := OCaml.Effect.State.global 15.

Definition b (x : unit)
  : M [ Effect.State.state Z; a_state ] (Effect.State.t Z) :=
  match x with
  | tt => a
  end.

Definition a_state_1 := OCaml.Effect.State.global_state.
Definition a_1 : M [ OCaml.Effect.State.state string; a_state_1 ]
  (OCaml.Effect.State.t string) := OCaml.Effect.State.global "test" % string.

Definition c (x : unit)
  : M [ Effect.State.state string; a_state_1 ] (Effect.State.t string) :=
  match x with
  | tt => a_1
  end.

Definition d : Z := 15.

Definition e : Z := d.

Definition d_1 : string := "test" % string.

Definition f : string := d_1.

Parameter op_eq : forall {A : Type}, A -> A -> bool.

Definition g {A : Type} (x : A) (y : A) : bool := op_eq x y.

Parameter op_eq_1 : forall {A : Type}, A -> A -> bool.

Definition h {A : Type} (x : A) (y : A) : bool := op_eq_1 x y.
