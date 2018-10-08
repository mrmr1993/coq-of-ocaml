Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition f {A B C : Type} (x : A)
  : M [ IO ] (B -> M [ exception failure ] C) :=
  let! _ := Pervasives.print_string "Hi" % string in
  ret (fun y => Pervasives.failwith "Bye" % string).

Definition r {A B : Type} (x : A) : M [ IO; exception failure ] B :=
  match x with
  | _ =>
    let! x_1 := lift [_;_] "10" (f 1) in
    lift [_;_] "01" (x_1 2)
  end.
