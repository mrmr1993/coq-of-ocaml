Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition r : OCaml.Effect.State.t Z := OCaml.Effect.State.init 12.
Definition r_state := OCaml.Effect.State.state nat.

Definition plus_one {A : Type} (x : A)
  : M [ OCaml.Effect.State.state Z; r_state ] Z :=
  match x with
  | _ =>
    let! x_1 :=
      let! x_1 :=
        let! x_1 := lift [_;_] "10" (OCaml.Effect.State.peekstate tt) in
        lift [_;_] "01" (OCaml.Effect.State.global r x_1) in
      lift [_;_] "10" (OCaml.Effect.State.read x_1) in
    ret (Z.add x_1 1)
  end.

Definition s : OCaml.Effect.State.t string := OCaml.Effect.State.init
  "Hi" % string.
Definition s_state := OCaml.Effect.State.state nat.

Definition fail {A B : Type} (x : A)
  : M [ OCaml.Effect.State.state string; OCaml.Failure; s_state ] B :=
  match x with
  | _ =>
    let! x_1 :=
      lift [_;_;_] "101"
        (let! x_1 :=
          let! x_1 := lift [_;_] "10" (OCaml.Effect.State.peekstate tt) in
          lift [_;_] "01" (OCaml.Effect.State.global s x_1) in
        lift [_;_] "10" (OCaml.Effect.State.read x_1)) in
    lift [_;_;_] "010" (OCaml.Pervasives.failwith x_1)
  end.

Definition reset {A : Type} (x : A)
  : M [ OCaml.Effect.State.state Z; r_state ] unit :=
  match x with
  | _ =>
    let! x_1 :=
      let! x_1 := lift [_;_] "10" (OCaml.Effect.State.peekstate tt) in
      lift [_;_] "01" (OCaml.Effect.State.global r x_1) in
    lift [_;_] "10" (OCaml.Effect.State.write x_1 0)
  end.

Definition incr {A : Type} (x : A)
  : M [ OCaml.Effect.State.state Z; r_state ] unit :=
  match x with
  | _ =>
    let! x_1 :=
      let! x_1 := lift [_;_] "10" (OCaml.Effect.State.peekstate tt) in
      lift [_;_] "01" (OCaml.Effect.State.global r x_1) in
    let! x_2 :=
      let! x_2 :=
        let! x_2 :=
          let! x_2 := lift [_;_] "10" (OCaml.Effect.State.peekstate tt) in
          lift [_;_] "01" (OCaml.Effect.State.global r x_2) in
        lift [_;_] "10" (OCaml.Effect.State.read x_2) in
      ret (Z.add x_2 1) in
    lift [_;_] "10" (OCaml.Effect.State.write x_1 x_2)
  end.
