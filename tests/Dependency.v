Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition a : string := "false" % string.

Definition b (x : unit) : M [ IO ] unit :=
  match x with
  | tt => OCaml.Pervasives.print_string "true" % string
  end.

Module C.
  Definition c : unit -> M [ IO ] string := OCaml.Pervasives.read_line.
End C.
