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
  : M [ OCaml.exception OCaml.match_failure ] B :=
  match x with
  | _ => OCaml.Pervasives.raise (OCaml.Match_failure (("error" % string, 1, 2)))
  end.

Definition e_assert {A B : Type} (x : A)
  : M [ OCaml.exception OCaml.assert_failure ] B :=
  match x with
  | _ =>
    OCaml.Pervasives.raise (OCaml.Assert_failure (("error" % string, 1, 2)))
  end.

Definition e_invalid {A B : Type} (x : A)
  : M [ OCaml.exception OCaml.invalid_argument ] B :=
  match x with
  | _ => OCaml.Pervasives.raise (OCaml.Invalid_argument ("error" % string))
  end.

Definition e_failure {A B : Type} (x : A)
  : M [ OCaml.exception OCaml.failure ] B :=
  match x with
  | _ => OCaml.Pervasives.raise (OCaml.Failure ("error" % string))
  end.

Definition e_not_found {A B : Type} (x : A)
  : M [ OCaml.exception OCaml.not_found ] B :=
  match x with
  | _ => OCaml.Pervasives.raise (OCaml.Not_found tt)
  end.

Definition e_out_of_mem {A B : Type} (x : A)
  : M [ OCaml.exception OCaml.out_of_memory ] B :=
  match x with
  | _ => OCaml.Pervasives.raise (OCaml.Out_of_memory tt)
  end.

Definition e_overflow {A B : Type} (x : A)
  : M [ OCaml.exception OCaml.stack_overflow ] B :=
  match x with
  | _ => OCaml.Pervasives.raise (OCaml.Stack_overflow tt)
  end.

Definition e_sys_err {A B : Type} (x : A)
  : M [ OCaml.exception OCaml.sys_error ] B :=
  match x with
  | _ => OCaml.Pervasives.raise (OCaml.Sys_error ("error" % string))
  end.

Definition e_EOF {A B : Type} (x : A)
  : M [ OCaml.exception OCaml.end_of_file ] B :=
  match x with
  | _ => OCaml.Pervasives.raise (OCaml.End_of_file tt)
  end.

Definition e_div {A B : Type} (x : A)
  : M [ OCaml.exception OCaml.division_by_zero ] B :=
  match x with
  | _ => OCaml.Pervasives.raise (OCaml.Division_by_zero tt)
  end.

Definition e_sys_blocked {A B : Type} (x : A)
  : M [ OCaml.exception OCaml.sys_blocked_io ] B :=
  match x with
  | _ => OCaml.Pervasives.raise (OCaml.Sys_blocked_io tt)
  end.

Definition e_rec_module {A B : Type} (x : A)
  : M [ OCaml.exception OCaml.undefined_recursive_module ] B :=
  match x with
  | _ =>
    OCaml.Pervasives.raise
      (OCaml.Undefined_recursive_module (("error" % string, 1, 2)))
  end.
