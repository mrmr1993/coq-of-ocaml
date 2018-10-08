Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition e_invalid {A B : Type} (x : A)
  : M [ OCaml.exception OCaml.invalid_argument ] B :=
  match x with
  | _ => Pervasives.invalid_arg "error" % string
  end.

Definition e_failure {A B : Type} (x : A)
  : M [ OCaml.exception OCaml.failure ] B :=
  match x with
  | _ => Pervasives.failwith "error" % string
  end.

Definition e_exit1 {A B : Type} (x : A)
  : M [ OCaml.exception Pervasives.exit ] B :=
  match x with
  | _ => Pervasives.raise (Pervasives.Exit tt)
  end.

Definition e_exit2 {A B : Type} (x : A)
  : M [ OCaml.exception Pervasives.exit ] B :=
  match x with
  | _ => Pervasives.raise (Pervasives.Exit tt)
  end.

Definition b_eq : bool := equiv_decb 1 2.

Definition b_neq1 : bool := nequiv_decb true false.

Definition b_neq2 : bool := nequiv_decb tt tt.

Definition b_lt : bool := Pervasives.lt 1 2.

Definition b_gt : bool := Pervasives.gt 1 2.

Definition b_le : bool := Pervasives.le true false.

Definition b_ge : bool := Pervasives.ge tt tt.

Definition comp : Z := Pervasives.compare 1 2.

Definition n_min : Z := Pervasives.min 1 2.

Definition n_max : Z := Pervasives.max 1 2.

Definition b_not : bool := negb false.

Definition b_and : bool := andb true false.

Definition b_and_old : bool := andb true false.

Definition b_or : bool := orb true false.

Definition b_or_old : bool := orb true false.

Definition app1 : Z := Pervasives.reverse_apply 12 (fun x => x).

Definition app2 : Z := apply (fun x => x) 12.

Definition n_neg1 : Z := Z.opp 12.

Definition n_neg2 : Z := (-12).

Definition n_pos1 : Z := 12.

Definition n_pos2 : Z := 12.

Definition n_succ : Z := Z.succ 1.

Definition n_pred : Z := Z.pred 1.

Definition n_plus : Z := Z.add 1 2.

Definition n_minus : Z := Z.sub 1 2.

Definition n_times : Z := Z.mul 1 2.

Definition n_div : Z := Z.div 1 2.

Definition n_mod : Z := Z.modulo 1 2.

Definition n_abs : Z := Z.abs 1.

Definition n_land : Z := Z.land 12 13.

Definition n_lor : Z := Z.lor 12 13.

Definition n_lxor : Z := Z.lxor 12 13.

Definition n_lsl : Z := Z.shiftl 12 13.

Definition n_lsr : Z := Z.shiftr 12 13.

Definition ss : string := String.append "begin" % string "end" % string.

Definition n_char : Z := Pervasives.int_of_char "c" % char.

Definition char_n {A : Type} (x : A)
  : M [ OCaml.exception invalid_argument ] ascii :=
  match x with
  | _ => Pervasives.char_of_int 23
  end.

Definition i : unit := Pervasives.ignore 12.

Definition s_bool : string := Pervasives.string_of_bool false.

Definition bool_s : bool := Pervasives.bool_of_string "false" % string.

Definition s_n : string := Pervasives.string_of_int 12.

Definition n_s : Z := Pervasives.int_of_string "12" % string.

Definition n1 : Z := fst (12, 13).

Definition n2 : Z := snd (12, 13).

Definition ll : list Z :=
  Pervasives.app (cons 1 (cons 2 [])) (cons 3 (cons 4 [])).

Definition p_c {A : Type} (x : A) : M [ IO ] unit :=
  match x with
  | _ => Pervasives.print_char "c" % char
  end.

Definition p_s {A : Type} (x : A) : M [ IO ] unit :=
  match x with
  | _ => Pervasives.print_string "str" % string
  end.

Definition p_n {A : Type} (x : A) : M [ IO ] unit :=
  match x with
  | _ => Pervasives.print_int 12
  end.

Definition p_endline {A : Type} (x : A) : M [ IO ] unit :=
  match x with
  | _ => Pervasives.print_endline "str" % string
  end.

Definition p_newline {A : Type} (x : A) : M [ IO ] unit :=
  match x with
  | _ => Pervasives.print_newline tt
  end.

Definition perr_c {A : Type} (x : A) : M [ IO ] unit :=
  match x with
  | _ => Pervasives.prerr_char "c" % char
  end.

Definition perr_s {A : Type} (x : A) : M [ IO ] unit :=
  match x with
  | _ => Pervasives.prerr_string "str" % string
  end.

Definition perr_n {A : Type} (x : A) : M [ IO ] unit :=
  match x with
  | _ => Pervasives.prerr_int 12
  end.

Definition perr_endline {A : Type} (x : A) : M [ IO ] unit :=
  match x with
  | _ => Pervasives.prerr_endline "str" % string
  end.

Definition perr_newline {A : Type} (x : A) : M [ IO ] unit :=
  match x with
  | _ => Pervasives.prerr_newline tt
  end.

Definition r_s {A : Type} (x : A) : M [ IO ] string :=
  match x with
  | _ => Pervasives.read_line tt
  end.

Definition r_n {A : Type} (x : A) : M [ IO ] Z :=
  match x with
  | _ => Pervasives.read_int tt
  end.
