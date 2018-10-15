Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Module M.
  Definition f {A B : Type} (x : A) : M [ exception failure ] B :=
    match x with
    | _ => Pervasives.failwith "failure" % string
    end.
End M.

Module N.
  Definition f {A B : Type} (x : A) : M [ exception assert_failure ] B :=
    match x with
    | _ => assert false
    end.
  
  Definition x : unit :=
    match Exception.run 0 (f tt) tt with
    | inl x => x
    | inr (Assert_failure (_)) => tt
    end.
  
  Import M.
  
  Definition y : unit :=
    match Exception.run 0 (M.f tt) tt with
    | inl x_1 => x_1
    | inr (Failure (_)) => tt
    end.
End N.

Definition b : unit :=
  match Exception.run 0 (N.f tt) tt with
  | inl x => x
  | inr (Assert_failure (_)) => tt
  end.

Import N.

Definition b' : unit :=
  match Exception.run 0 (N.f tt) tt with
  | inl x => x
  | inr (Assert_failure (_)) => tt
  end.

Definition x : Z := 15.

Module A.
  Definition x {A B : Type} (x : A) : M [ exception assert_failure ] B :=
    match x with
    | _ => assert false
    end.
End A.

Module B.
  Definition a : Z := x.
  
  Import A.
  
  Definition b {A B : Type} : A -> M [ exception assert_failure ] B := x.
  
  Definition x {A B : Type} (x : A) : M [ exception failure ] B :=
    match x with
    | _ => Pervasives.failwith "failure" % string
    end.
  
  Definition c {A B : Type} : A -> M [ exception failure ] B := x.
End B.

Module C.
  Definition a : Z := x.
  
  Definition x {A B : Type} (x : A) : M [ exception failure ] B :=
    match x with
    | _ => Pervasives.failwith "failure" % string
    end.
  
  Definition b {A B : Type} : A -> M [ exception failure ] B := x.
  
  Import A.
  
  Definition c {A B : Type} : A -> M [ exception assert_failure ] B := A.x.
End C.

Module D.
  Module A.
    Definition a : Z := 2.
  End A.
  
  Definition b : Z := x.
  
  Import A.
  
  Definition c : Z := A.a.
  
  Definition d : Z := x.
End D.
