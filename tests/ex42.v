Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition x (a : Z) (b : Z) : M [ OCaml.Effect.State.state Z ] Z :=
  let! y := OCaml.Pervasives.ref 0 in
  let! _ :=
    OCaml.Basics.for_to a b
      (fun i =>
        let! x :=
          let! x := OCaml.Effect.State.read y in
          ret (Z.add x 1) in
        OCaml.Effect.State.write y x) in
  OCaml.Effect.State.read y.

Definition nested (x : Z) (y : Z)
  : M [ OCaml.Effect.State.state (list bool) ] (list bool) :=
  let! a := OCaml.Pervasives.ref [] in
  let! _ :=
    OCaml.Basics.for_to 0 x
      (fun i =>
        let! _ :=
          OCaml.Basics.for_to 0 y
            (fun j =>
              let! x_1 :=
                let! x_1 := OCaml.Effect.State.read a in
                ret (cons true x_1) in
              OCaml.Effect.State.write a x_1) in
        let! x_1 :=
          let! x_1 := OCaml.Effect.State.read a in
          ret (cons false x_1) in
        OCaml.Effect.State.write a x_1) in
  OCaml.Effect.State.read a.

Definition raises (x : Z) : M [ OCaml.exception OCaml.failure ] unit :=
  OCaml.Basics.for_to 0 x
    (fun i =>
      (OCaml.Pervasives.failwith "x is not less than 0" % string) :
        M [ OCaml.exception OCaml.failure ] unit).

Definition complex_raises (x : Z) : M [ OCaml.exception OCaml.failure ] unit :=
  let f {A B : Type} (a : A)
    : M [ OCaml.exception OCaml.failure ] (A * Z * B) :=
    let! x_1 := OCaml.Pervasives.failwith "x is not less than 0" % string in
    ret (a, 15, x_1) in
  OCaml.Basics.for_to 0 x
    (fun i => (f true) : M [ OCaml.exception OCaml.failure ] (bool * Z * unit)).

Definition argument_effects (x : OCaml.Effect.State.t Z) (y : Z)
  : M [ OCaml.Effect.State.state Z ] Z :=
  let! y := OCaml.Pervasives.ref y in
  let! z := OCaml.Pervasives.ref 0 in
  let! _ :=
    let! x_1 := OCaml.Effect.State.read x in
    OCaml.Basics.for_to 0 x_1
      (fun i =>
        let! _ :=
          let! x_1 := OCaml.Effect.State.read y in
          OCaml.Basics.for_to 0 x_1
            (fun j =>
              let! x_1 :=
                let! x_1 := OCaml.Effect.State.read z in
                ret (Z.add x_1 1) in
              OCaml.Effect.State.write z x_1) in
        let! x_1 :=
          let! x_1 := OCaml.Effect.State.read y in
          ret (Z.sub x_1 1) in
        OCaml.Effect.State.write y x_1) in
  OCaml.Effect.State.read z.
