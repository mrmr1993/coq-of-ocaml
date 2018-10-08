Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition n : Z := 12.

Definition c1 : ascii := "a" % char.

Definition c2 : ascii := "010" % char.

Definition c3 : ascii := "009" % char.

Definition c4 : ascii := """" % char.

Definition s : string := "hi
	:)""" % string.

Definition b1 : bool := false.

Definition b2 : bool := true.

Definition u : unit := tt.

Definition l1 {A : Type} : list A := [].

Definition l2 : list Z := cons 0 (cons 1 (cons 2 (cons 3 []))).

Definition o : option Z :=
  if b1 then
    None
  else
    Some n.

Definition e_match {A B : Type} (x : A)
  : M [ OCaml.exception match_failure ] B :=
  match x with
  | _ => Pervasives.raise (Match_failure (("error" % string, 1, 2)))
  end.

Definition e_assert {A B : Type} (x : A)
  : M [ OCaml.exception assert_failure ] B :=
  match x with
  | _ => Pervasives.raise (Assert_failure (("error" % string, 1, 2)))
  end.

Definition e_invalid {A B : Type} (x : A)
  : M [ OCaml.exception invalid_argument ] B :=
  match x with
  | _ => Pervasives.raise (Invalid_argument ("error" % string))
  end.

Definition e_failure {A B : Type} (x : A) : M [ OCaml.exception failure ] B :=
  match x with
  | _ => Pervasives.raise (Failure ("error" % string))
  end.

Definition e_not_found {A B : Type} (x : A)
  : M [ OCaml.exception not_found ] B :=
  match x with
  | _ => Pervasives.raise (Not_found tt)
  end.

Definition e_out_of_mem {A B : Type} (x : A)
  : M [ OCaml.exception out_of_memory ] B :=
  match x with
  | _ => Pervasives.raise (Out_of_memory tt)
  end.

Definition e_overflow {A B : Type} (x : A)
  : M [ OCaml.exception stack_overflow ] B :=
  match x with
  | _ => Pervasives.raise (Stack_overflow tt)
  end.

Definition e_sys_err {A B : Type} (x : A) : M [ OCaml.exception sys_error ] B :=
  match x with
  | _ => Pervasives.raise (Sys_error ("error" % string))
  end.

Definition e_EOF {A B : Type} (x : A) : M [ OCaml.exception end_of_file ] B :=
  match x with
  | _ => Pervasives.raise (End_of_file tt)
  end.

Definition e_div {A B : Type} (x : A)
  : M [ OCaml.exception division_by_zero ] B :=
  match x with
  | _ => Pervasives.raise (Division_by_zero tt)
  end.

Definition e_sys_blocked {A B : Type} (x : A)
  : M [ OCaml.exception sys_blocked_io ] B :=
  match x with
  | _ => Pervasives.raise (Sys_blocked_io tt)
  end.

Definition e_rec_module {A B : Type} (x : A)
  : M [ OCaml.exception undefined_recursive_module ] B :=
  match x with
  | _ =>
    Pervasives.raise (Undefined_recursive_module (("error" % string, 1, 2)))
  end.
