Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Module A.
  Definition a : Z := 5.
  
  Definition c {A : Type} (x : string)
    : M [ OCaml.exception OCaml.Failure ] A := OCaml.Pervasives.failwith x.
End A.

Include A.

Definition b : Z := Z.add a 2.

Definition d {A : Type} (b : bool) : M [ OCaml.exception OCaml.Failure ] A :=
  if b then
    c "true" % string
  else
    c "false" % string.
