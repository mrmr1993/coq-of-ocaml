Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Require Tests.DependEx38.

Import DependEx38.

Definition f {A B : Type} : A -> B -> A := f.

Definition m : Z := n.
