Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition a : OCaml.Effect.State.t Z := OCaml.Effect.State.init 15.
Definition a_state := OCaml.Effect.State.state nat.

Definition b (x : unit)
  : M [ OCaml.Effect.State.state Z; a_state ] (OCaml.Effect.State.t Z) :=
  match x with
  | tt =>
    let! x_1 := lift [_;_] "10" (OCaml.Effect.State.peekstate tt) in
    lift [_;_] "01" (OCaml.Effect.State.global a x_1)
  end.

Definition a_1 : OCaml.Effect.State.t string := OCaml.Effect.State.init
  "test" % string.
Definition a_state_1 := OCaml.Effect.State.state nat.

Definition c (x : unit)
  : M [ OCaml.Effect.State.state string; a_state_1 ]
    (OCaml.Effect.State.t string) :=
  match x with
  | tt =>
    let! x_1 := lift [_;_] "10" (OCaml.Effect.State.peekstate tt) in
    lift [_;_] "01" (OCaml.Effect.State.global a_1 x_1)
  end.

Definition d : Z := 15.

Definition e : Z := d.

Definition d_1 : string := "test" % string.

Definition f : string := d_1.

Parameter op_eq : forall {A : Type}, A -> A -> bool.

Definition g {A : Type} (x : A) (y : A) : bool := op_eq x y.

Parameter op_eq_1 : forall {A : Type}, A -> A -> bool.

Definition h {A : Type} (x : A) (y : A) : bool := op_eq_1 x y.
