Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Inductive fail : Type :=
| Fail : (string) -> fail.

Definition div (n : Z) : M [ exception fail ] Z :=
  if equiv_decb n 0 then
    Pervasives.raise (Fail ("n is null" % string))
  else
    ret (Z.div 256 n).
