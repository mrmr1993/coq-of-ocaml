Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition get_local_ref (tt : unit) : M [ OCaml.Effect.State.state Z ] Z :=
  let! x := OCaml.Pervasives.ref 12 in
  OCaml.Effect.State.read x.

Definition set_local_ref (tt : unit) : M [ OCaml.Effect.State.state Z ] Z :=
  let! x := OCaml.Pervasives.ref 12 in
  let! _ := OCaml.Effect.State.write x 15 in
  OCaml.Effect.State.read x.

Definition add_multiple_by_refs (a : Z) (b : Z) (c : Z) (d : Z)
  : M [ OCaml.Effect.State.state Z ] Z :=
  let! x := OCaml.Pervasives.ref a in
  let! _ :=
    let! x_1 :=
      let! x_1 := OCaml.Effect.State.read x in
      ret (Z.add x_1 b) in
    OCaml.Effect.State.write x x_1 in
  let! y := OCaml.Pervasives.ref c in
  let! _ :=
    let! x_1 :=
      let! x_1 := OCaml.Effect.State.read y in
      ret (Z.add x_1 d) in
    OCaml.Effect.State.write y x_1 in
  let! z :=
    let! x_1 :=
      let! x_1 := OCaml.Effect.State.read x in
      let! x_2 := OCaml.Effect.State.read y in
      ret (Z.add x_1 x_2) in
    OCaml.Pervasives.ref x_1 in
  OCaml.Effect.State.read z.

Definition set_ref (x : OCaml.Effect.State.t Z)
  : M [ OCaml.Effect.State.state Z ] unit := OCaml.Effect.State.write x 15.

Definition get_ref (x : OCaml.Effect.State.t Z)
  : M [ OCaml.Effect.State.state Z ] Z := OCaml.Effect.State.read x.

Definition update_ref (x : OCaml.Effect.State.t Z)
  : M [ OCaml.Effect.State.state Z ] unit :=
  let! x_1 :=
    let! x_1 := OCaml.Effect.State.read x in
    ret (Z.add x_1 5) in
  OCaml.Effect.State.write x x_1.

Definition new_ref (x : unit)
  : M [ OCaml.Effect.State.state Z ] (OCaml.Effect.State.t Z) :=
  OCaml.Pervasives.ref 15.

Definition r : OCaml.Effect.State.t Z := OCaml.Effect.State.init 18.
Definition r_state := nat.

Definition set_r (x : unit)
  : M [ OCaml.Effect.State.state Z; OCaml.Effect.State.state r_state ] unit :=
  let! x_1 :=
    let! x_1 := lift [_;_] "10" (OCaml.Effect.State.peekstate tt) in
    lift [_;_] "01" (OCaml.Effect.State.global r x_1) in
  lift [_;_] "10" (set_ref x_1).

Definition get_r (x : unit)
  : M [ OCaml.Effect.State.state Z; OCaml.Effect.State.state r_state ] Z :=
  let! x_1 :=
    let! x_1 := lift [_;_] "10" (OCaml.Effect.State.peekstate tt) in
    lift [_;_] "01" (OCaml.Effect.State.global r x_1) in
  lift [_;_] "10" (get_ref x_1).

Definition r_add_15 (x : unit)
  : M [ OCaml.Effect.State.state Z; OCaml.Effect.State.state r_state ] Z :=
  let! i := get_r tt in
  let! _ := set_r tt in
  let! j := get_r tt in
  let! _ :=
    let! x_1 :=
      let! x_1 := lift [_;_] "10" (OCaml.Effect.State.peekstate tt) in
      lift [_;_] "01" (OCaml.Effect.State.global r x_1) in
    lift [_;_] "10" (OCaml.Effect.State.write x_1 (Z.add i j)) in
  let! x_1 :=
    let! x_1 := lift [_;_] "10" (OCaml.Effect.State.peekstate tt) in
    lift [_;_] "01" (OCaml.Effect.State.global r x_1) in
  lift [_;_] "10" (OCaml.Effect.State.read x_1).
