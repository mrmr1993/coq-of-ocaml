Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition t := Effect.Open_Type.t.

Definition f (x : unit) : M [ exception assert_failure ] (t [ ]) :=
  match x with
  | tt => assert false
  end.

Definition u := Effect.Open_Type.t.

Definition g {A : Type} (x : A) : M [ exception failure ] (u [ ]) :=
  Pervasives.failwith "fail" % string.

Polymorphic
Inductive t_1 : Type :=
| Test1 : t_1
| Test2 : bool -> t_1.

Polymorphic
Inductive t_2 : Type :=
| Test3 : Z -> t_2
| Test4 : (option Z) -> t_2.

Polymorphic
Inductive u_1 (b : Type) : Type :=
| Test5 : b -> u_1 b
| Test6 : Z -> u_1 b.
Arguments Test5 {b} _.
Arguments Test6 {b} _.

Definition x : t [ t_1 : Type ] := inl Test1.

Definition y : u [ u_1 Z ] := inl (Test5 5).

Definition z {A : Type} : u [ u_1 A ] := inl (Test6 6).

Definition failure : exn [ failure : Type ] := inl (Failure "" % string).
