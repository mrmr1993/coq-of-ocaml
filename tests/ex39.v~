Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition get_local_ref (tt : unit) : M [ OCaml.Effect.State.state ] Z :=
  let! x := OCaml.Pervasives.ref 12 in
  OCaml.Effect.State.read x.

Definition set_local_ref (tt : unit) : M [ OCaml.Effect.State.state ] Z :=
  let! x := OCaml.Pervasives.ref 12 in
  let! _ := OCaml.Effect.State.write x 15 in
  OCaml.Effect.State.read x.

Definition add_multiple_by_refs (a : Z) (b : Z) (c : Z) (d : Z)
  : M [ OCaml.Effect.State.state ] Z :=
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
