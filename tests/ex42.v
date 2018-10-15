Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition x (a : Z) (b : Z) : M [ Effect.State.state Z ] Z :=
  let! y := Pervasives.ref 0 in
  let! _ :=
    Basics.for_to a b
      (fun i =>
        let! x :=
          let! x := Effect.State.read y in
          ret (Z.add x 1) in
        Effect.State.write y x) in
  Effect.State.read y.

Definition nested (x : Z) (y : Z)
  : M [ Effect.State.state (list bool) ] (list bool) :=
  let! a := Pervasives.ref [] in
  let! _ :=
    Basics.for_to 0 x
      (fun i =>
        let! _ :=
          Basics.for_to 0 y
            (fun j =>
              let! x_1 :=
                let! x_1 := Effect.State.read a in
                ret (cons true x_1) in
              Effect.State.write a x_1) in
        let! x_1 :=
          let! x_1 := Effect.State.read a in
          ret (cons false x_1) in
        Effect.State.write a x_1) in
  Effect.State.read a.

Definition raises (x : Z) : M [ exception failure ] unit :=
  Basics.for_to 0 x
    (fun i =>
      (Pervasives.failwith "x is not less than 0" % string) :
        M [ exception failure ] unit).

Definition complex_raises (x : Z) : M [ exception failure ] unit :=
  let f {A B : Type} (a : A) : M [ exception failure ] (A * Z * B) :=
    let! x_1 := Pervasives.failwith "x is not less than 0" % string in
    ret (a, 15, x_1) in
  Basics.for_to 0 x
    (fun i => (f true) : M [ exception failure ] (bool * Z * unit)).

Definition argument_effects (x : Effect.State.t Z) (y : Z)
  : M [ Effect.State.state Z ] Z :=
  let! y := Pervasives.ref y in
  let! z := Pervasives.ref 0 in
  let! _ :=
    let! x_1 := Effect.State.read x in
    Basics.for_to 0 x_1
      (fun i =>
        let! _ :=
          let! x_1 := Effect.State.read y in
          Basics.for_to 0 x_1
            (fun j =>
              let! x_1 :=
                let! x_1 := Effect.State.read z in
                ret (Z.add x_1 1) in
              Effect.State.write z x_1) in
        let! x_1 :=
          let! x_1 := Effect.State.read y in
          ret (Z.sub x_1 1) in
        Effect.State.write y x_1) in
  Effect.State.read z.
