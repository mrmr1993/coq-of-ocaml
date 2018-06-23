Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition r := OCaml.Effect.State.init 12.
Definition r_state := @OCaml.Effect.State.state Z.

Definition plus_one {A : Type} (x : A) : M [ OCaml.Effect.State.state ] Z :=
  match x with
  | _ =>
    let! x_1 := OCaml.Effect.State.read r in
    ret (Z.add x_1 1)
  end.

Definition s := OCaml.Effect.State.init "Hi" % string.
Definition s_state := @OCaml.Effect.State.state string.

Definition fail {A B : Type} (x : A)
  : M [ OCaml.Failure; OCaml.Effect.State.state ] B :=
  match x with
  | _ =>
    let! x_1 := lift [_;_] "01" (OCaml.Effect.State.read s) in
    lift [_;_] "10" (OCaml.Pervasives.failwith x_1)
  end.

Definition reset {A : Type} (x : A) : M [ OCaml.Effect.State.state ] unit :=
  match x with
  | _ => OCaml.Effect.State.write r 0
  end.

Definition incr {A : Type} (x : A) : M [ OCaml.Effect.State.state ] unit :=
  match x with
  | _ =>
    let! x_1 :=
      let! x_1 := OCaml.Effect.State.read r in
      ret (Z.add x_1 1) in
    OCaml.Effect.State.write r x_1
  end.
