Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Require Tests.DependEx38.

Import Tests.DependEx38.

Definition f {A B : Type} : A -> B -> A := Tests.DependEx38.f.

Definition m : Z := Tests.DependEx38.n.
