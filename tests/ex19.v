Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Inductive error : Type :=
| Error : unit -> error.

Definition x1 : Z :=
  match Exception.run 0 (Pervasives.raise (Error tt)) tt with
  | inl x => x
  | inr (Error tt) => 12
  end.

Definition x2 {A B : Type} (x : A) : M [ OCaml.exception OCaml.failure ] B :=
  match x with
  | _ =>
    match Exception.run 0 (Pervasives.raise (Error tt)) tt with
    | inl x => ret x
    | inr (Error tt) => Pervasives.failwith "arg" % string
    end
  end.

Definition x3 (b : bool) : M [ OCaml.exception OCaml.failure ] Z :=
  let! x :=
    Exception.run 0
      (if b then
        lift [_;_] "01" (Pervasives.failwith "arg" % string)
      else
        lift [_;_] "10" (Pervasives.raise (Error tt))) tt in
  match x with
  | inl x => ret x
  | inr (Error tt) => ret 12
  end.
