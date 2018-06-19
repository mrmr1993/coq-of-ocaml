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
