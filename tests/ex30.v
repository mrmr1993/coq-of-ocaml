Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Module M.
  Definition f {A B : Type} (x : A) : M [ OCaml.exception OCaml.Failure ] B :=
    match x with
    | _ => OCaml.Pervasives.failwith "failure" % string
    end.
End M.

Module N.
  Definition f {A B : Type} (x : A)
    : M [ OCaml.exception OCaml.Assert_failure ] B :=
    match x with
    | _ => OCaml.assert false
    end.
  
  Definition x : unit :=
    match Exception.run 0 (f tt) tt with
    | inl x => x
    | inr (_) => tt
    end.
  
  Import M.
  
  Definition y : unit :=
    match Exception.run 0 (M.f tt) tt with
    | inl x_1 => x_1
    | inr (_) => tt
    end.
End N.

Definition b : unit :=
  match Exception.run 0 (N.f tt) tt with
  | inl x => x
  | inr (_) => tt
  end.

Import N.

Definition b' : unit :=
  match Exception.run 0 (N.f tt) tt with
  | inl x => x
  | inr (_) => tt
  end.

Definition x : Z := 15.

Module A.
  Definition x {A B : Type} (x : A)
    : M [ OCaml.exception OCaml.Assert_failure ] B :=
    match x with
    | _ => OCaml.assert false
    end.
End A.

Module B.
  Definition a : Z := x.
  
  Import A.
  
  Definition b {A B : Type}
    : A -> M [ OCaml.exception OCaml.Assert_failure ] B := x.
  
  Definition x {A B : Type} (x : A) : M [ OCaml.exception OCaml.Failure ] B :=
    match x with
    | _ => OCaml.Pervasives.failwith "failure" % string
    end.
  
  Definition c {A B : Type} : A -> M [ OCaml.exception OCaml.Failure ] B := x.
End B.

Module C.
  Definition a : Z := x.
  
  Definition x {A B : Type} (x : A) : M [ OCaml.exception OCaml.Failure ] B :=
    match x with
    | _ => OCaml.Pervasives.failwith "failure" % string
    end.
  
  Definition b {A B : Type} : A -> M [ OCaml.exception OCaml.Failure ] B := x.
  
  Import A.
  
  Definition c {A B : Type}
    : A -> M [ OCaml.exception OCaml.Assert_failure ] B := A.x.
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
