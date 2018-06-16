Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition r := Effect.make Z Empty_set.

Definition read_r (_ : unit) : M [ r ] Z :=
  State.read r tt.

Definition write_r (x : Z) : M [ r ] unit :=
  State.write r x.

Definition plus_one {A : Type} (x : A) : M [ r ] Z :=
  match x with
  | _ =>
    let! x_1 := OCaml.Effect.State.read r tt in
    ret (Z.add x_1 1)
  end.

Definition s := Effect.make string Empty_set.

Definition read_s (_ : unit) : M [ s ] string :=
  State.read s tt.

Definition write_s (x : string) : M [ s ] unit :=
  State.write s x.

Definition fail {A B : Type} (x : A) : M [ s; OCaml.Failure ] B :=
  match x with
  | _ =>
    let! x_1 := lift [_;_] "10" (OCaml.Effect.State.read s tt) in
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
      let! x_1 := OCaml.Effect.State.read r tt in
      ret (Z.add x_1 1) in
    OCaml.Effect.State.write r x_1
  end.
