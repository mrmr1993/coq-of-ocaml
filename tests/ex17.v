Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Inductive outside : Type :=
| Outside : unit -> outside.

Definition f {A B : Type} (x : A) : M [ OCaml.exception outside ] B :=
  Pervasives.raise (Outside tt).

Module G.
  Inductive inside : Type :=
  | Inside : (Z * string) -> inside.
  
  Definition g {A : Type} (b : bool)
    : M [ OCaml.exception outside; OCaml.exception inside ] A :=
    if b then
      lift [_;_] "01" (Pervasives.raise (Inside (12, "no" % string)))
    else
      lift [_;_] "10" (Pervasives.raise (Outside tt)).
End G.

Fixpoint h_rec {A B : Type} (counter : nat) (l : list A)
  : M [ IO; NonTermination; exception outside; exception G.inside ] B :=
  match counter with
  | O => lift [_;_;_;_] "0100" (not_terminated tt)
  | S counter =>
    match l with
    | [] =>
      lift [_;_;_;_] "1011"
        (let! _ :=
          lift [_;_;_] "100" (Pervasives.print_string "no tail" % string) in
        lift [_;_;_] "011" (G.g false))
    | cons x [] =>
      lift [_;_;_;_] "0001" (Pervasives.raise (G.Inside (0, "gg" % string)))
    | cons _ xs => (h_rec counter) xs
    end
  end.

Definition h {A B : Type} (l : list A)
  : M [ Counter; IO; NonTermination; exception outside; exception G.inside ] B :=
  let! x := lift [_;_;_;_;_] "10000" (read_counter tt) in
  lift [_;_;_;_;_] "01111" (h_rec x l).
