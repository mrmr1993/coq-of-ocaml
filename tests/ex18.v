Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition r_state := OCaml.Effect.State.global_state.
Definition r : M [ OCaml.Effect.State.state Z; r_state ]
  (OCaml.Effect.State.t Z) := OCaml.Effect.State.global 12.

Definition plus_one {A : Type} (x : A)
  : M [ OCaml.Effect.State.state Z; r_state ] Z :=
  match x with
  | _ =>
    let! x_1 :=
      let! x_1 := r in
      lift [_;_] "10" (Effect.State.read x_1) in
    ret (Z.add x_1 1)
  end.

Definition s_state := OCaml.Effect.State.global_state.
Definition s : M [ OCaml.Effect.State.state string; s_state ]
  (OCaml.Effect.State.t string) := OCaml.Effect.State.global "Hi" % string.

Definition fail {A B : Type} (x : A)
  : M
    [ OCaml.Effect.State.state string; s_state; OCaml.exception OCaml.failure ]
    B :=
  match x with
  | _ =>
    let! x_1 :=
      lift [_;_;_] "110"
        (let! x_1 := s in
        lift [_;_] "10" (Effect.State.read x_1)) in
    lift [_;_;_] "001" (Pervasives.failwith x_1)
  end.

Definition reset {A : Type} (x : A)
  : M [ OCaml.Effect.State.state Z; r_state ] unit :=
  match x with
  | _ =>
    let! x_1 := r in
    lift [_;_] "10" (Effect.State.write x_1 0)
  end.

Definition incr {A : Type} (x : A)
  : M [ OCaml.Effect.State.state Z; r_state ] unit :=
  match x with
  | _ =>
    let! x_1 := r in
    let! x_2 :=
      let! x_2 :=
        let! x_2 := r in
        lift [_;_] "10" (Effect.State.read x_2) in
      ret (Z.add x_2 1) in
    lift [_;_] "10" (Effect.State.write x_1 x_2)
  end.
