Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Inductive set : Type :=
| Empty : set
| Node : set -> Z -> set -> set .
Arguments Empty .
Arguments Node _ _ _.

Definition empty : set := Empty.

Fixpoint member_rec (counter : nat) (x : Z) (s : set) :
  M [ Err_NonTermination ] bool :=
  match counter with
  | 0 % nat => not_terminated tt
  | S counter =>
    match s with
    | Empty => ret false
    | Node s1 y s2 =>
      if (Z.ltb x) y then
        ((member_rec counter) x) s1
      else
        if (Z.ltb y) x then
          ((member_rec counter) x) s2
        else
          ret true
    end
  end.

Definition member (x : Z) (s : set) : M [ Ref_Counter; Err_NonTermination ] bool
  :=
  let! counter := lift [_;_] "10" (read_counter tt) in
  lift [_;_] "01" (((member_rec counter) x) s).

Fixpoint insert_rec (counter : nat) (x : Z) (s : set) :
  M [ Err_NonTermination ] set :=
  match counter with
  | 0 % nat => not_terminated tt
  | S counter =>
    match s with
    | Empty => ret (Node Empty x Empty)
    | Node s1 y s2 =>
      if (Z.ltb x) y then
        let! x := ((insert_rec counter) x) s1 in
        ret (Node x y s2)
      else
        if (Z.ltb y) x then
          let! x := ((insert_rec counter) x) s2 in
          ret (Node s1 y x)
        else
          ret s
    end
  end.

Definition insert (x : Z) (s : set) : M [ Ref_Counter; Err_NonTermination ] set
  :=
  let! counter := lift [_;_] "10" (read_counter tt) in
  lift [_;_] "01" (((insert_rec counter) x) s).