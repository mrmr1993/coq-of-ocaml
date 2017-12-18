Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Require Import Dependency.

Definition a : string := Dependency.a.

Definition b : unit -> M [ IO ] unit := Dependency.b.

Definition c : unit -> M [ IO ] string := Dependency.C.c.
