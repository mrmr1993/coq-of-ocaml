Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Module Type S_1.
  Parameter x : Z.
  
  Parameter y : bool.
  
  Parameter z : forall {A B C : Type}, (A -> B -> A * C) -> A -> (list B) -> C.
  Arguments z {A} {B} {C}.
  
  Inductive t : Type :=
  | Inductive1 : t
  | Inductive2 : Z -> t
  | Inductive3 : bool -> t.
  
  Definition u a := list (a * t).
  
  Module X.
    Parameter x : bool.
    
    Parameter y : Z.
  End X.
  
  Module Type S.
    Parameter x : bool.
    
    Parameter y : Z.
  End S.
End S_1.
