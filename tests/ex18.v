Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition r := Effect.make Z Empty_set.

Definition plus_one {A : Type} (x : A) : M [ r ] Z :=
  match x with
  | _ =>
    let! x_1 := OCaml.Effect.State.read r in
    ret (Z.add x_1 1)
  end.

Definition s := Effect.make string Empty_set.

Definition fail {A B : Type} (x : A) : M [ s; OCaml.Failure ] B :=
  match x with
  | _ =>
    let! x_1 := lift [_;_] "10" (OCaml.Effect.State.read s) in
    lift [_;_] "01" (OCaml.Pervasives.failwith x_1)
  end.

Definition reset {A : Type} (x : A) : M [ r ] unit :=
  match x with
  | _ => OCaml.Effect.State.write r 0
  end.

Definition incr {A : Type} (x : A) : M [ r ] unit :=
  match x with
  | _ =>
    let! x_1 :=
      let! x_1 := OCaml.Effect.State.read r in
      ret (Z.add x_1 1) in
    OCaml.Effect.State.write r x_1
  end.
