Require Import Libraries.
Require Import Effect.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

(* TODO: add floats, add the different integer types (int32, int64, ...). *)
Class OrderDec {A R} `(StrictOrder A R) := {
  compare : A -> A -> comparison;
  compare_is_sound : forall x y,
    CompareSpec (x = y) (R x y) (R y x) (compare x y) }.

Module Unit.
  Definition lt (x y : unit) : Prop := False.

  Instance strict_order : StrictOrder lt.
    refine {|
      StrictOrder_Irreflexive := _;
      StrictOrder_Transitive := _ |}.
    - intro x.
      unfold complement, lt.
      trivial.
    - intros x y z Rxy Ryz.
      exact Rxy.
  Qed.

  Instance order_dec : OrderDec strict_order.
    refine {|
      compare := fun x y => Eq;
      compare_is_sound := fun x y => CompEq _ _ _ |}.
    abstract (now destruct x; destruct y).
  Defined.
End Unit.

Module Bool.
  Inductive lt : bool -> bool -> Prop :=
  | lt_intro : lt false true.

  Instance strict_order : StrictOrder lt.
    refine {|
      StrictOrder_Irreflexive := _;
      StrictOrder_Transitive := _ |}.
    - intros x Hxx.
      inversion Hxx.
    - intros x y z Hxy Hyz.
      destruct Hxy; destruct Hyz.
      constructor.
  Qed.

  Instance order_dec : OrderDec strict_order.
    refine {|
      compare := fun x y =>
        match (x, y) with
        | (false, true) => Lt
        | (false, false) | (true, true) => Eq
        | (true, false) => Gt
        end;
      compare_is_sound := fun x y => _ |}.
    abstract (destruct x; destruct y;
      try apply CompLt; try apply CompEq; try apply CompGt;
      constructor).
  Defined.
End Bool.

Module Z.
  Instance eq_dec : EqDec (eq_setoid Z) := Z.eq_dec.

  Instance order_dec : OrderDec Z.lt_strorder := {|
    compare := Z.compare;
    compare_is_sound := Z.compare_spec |}.
End Z.

Definition Match_failure := Effect.make unit (string * Z * Z).
 Definition raise_Match_failure {A : Type} (x : string * Z * Z)
  : M [ Match_failure ] A :=
  fun s => (inr (inl x), s).

Definition Assert_failure := Effect.make unit (string * Z * Z).
Definition raise_Assert_failure {A : Type} (x : string * Z * Z)
  : M [ Assert_failure ] A :=
  fun s => (inr (inl x), s).

Definition Invalid_argument := Effect.make unit string.
Definition raise_Invalid_argument {A : Type} (x : string)
  : M [ Invalid_argument ] A :=
  fun s => (inr (inl x), s).

Definition Failure := Effect.make unit string.
Definition raise_Failure {A : Type} (x : string)
  : M [ Failure ] A :=
  fun s => (inr (inl x), s).

Definition Not_found := Effect.make unit unit.
Definition raise_Not_found {A : Type} (x : unit)
  : M [ Not_found ] A :=
  fun s => (inr (inl x), s).

Definition Out_of_memory := Effect.make unit unit.
Definition raise_Out_of_memory {A : Type} (x : unit)
  : M [ Out_of_memory ] A :=
  fun s => (inr (inl x), s).

Definition Stack_overflow := Effect.make unit unit.
Definition raise_Stack_overflow {A : Type} (x : unit)
  : M [ Stack_overflow ] A :=
  fun s => (inr (inl x), s).

Definition Sys_error := Effect.make unit string.
Definition raise_Sys_error {A : Type} (x : string)
  : M [ Sys_error ] A :=
  fun s => (inr (inl x), s).

Definition End_of_file := Effect.make unit unit.
Definition raise_End_of_file {A : Type} (x : unit)
  : M [ End_of_file ] A :=
  fun s => (inr (inl x), s).

Definition Division_by_zero := Effect.make unit unit.
Definition raise_Division_by_zero {A : Type} (x : unit)
  : M [ Division_by_zero ] A :=
  fun s => (inr (inl x), s).

Definition Sys_blocked_io := Effect.make unit unit.
Definition raise_Sys_blocked_io {A : Type} (x : unit)
  : M [ Sys_blocked_io ] A :=
  fun s => (inr (inl x), s).

Definition Undefined_recursive_module := Effect.make unit (string * Z * Z).
Definition raise_Undefined_recursive_module {A : Type} (x : string * Z * Z)
  : M [ Undefined_recursive_module ] A :=
  fun s => (inr (inl x), s).

Definition assert {A : Type} (b : bool) : M [Assert_failure] A :=
  raise_Assert_failure ("coq" % string, 0, 0).

Definition for_to {A : Type} {es : list Effect.t} (start_value end_value : Z)
  (f : Z -> M es A) : M es unit :=
  let fix for_to (n : nat) (value : Z) : M es unit :=
    match n with
    | O => let! _ := f value in ret tt
    | S n => let! _ := f value in for_to n (value + 1)
    end in
  let difference := end_value - start_value in
  match difference with
  | Zneg _ => Effect.of_raw (fun s => (inl tt, s))
  | Z0 => let! _ := f start_value in ret tt
  | Zpos pos => for_to (Pos.to_nat pos) start_value
  end.

Definition for_downto {A : Type} {es : list Effect.t}
  (start_value end_value : Z) (f : Z -> M es A) : M es unit :=
  let fix for_to (n : nat) (value : Z) : M es unit :=
    match n with
    | O => let! _ := f value in ret tt
    | S n => let! _ := f value in for_to n (value - 1)
    end in
  let difference := start_value - end_value in
  match difference with
  | Zneg _ => Effect.of_raw (fun s => (inl tt, s))
  | Z0 => let! _ := f end_value in ret tt
  | Zpos pos => for_to (Pos.to_nat pos) end_value
  end.

(** OCaml functions are converted to their Coq's counter parts when it is
    possible. *)
Module Pervasives.
  (** * Exceptions *)
  Definition invalid_arg {A : Type} (message : string)
    : M [Invalid_argument] A :=
    raise_Invalid_argument message.

  Definition failwith {A : Type} (message : string)
    : M [Failure] A :=
    raise_Failure message.

  Definition Exit := Effect.make unit unit.
  Definition raise_Exit {A : Type} (x : unit) : M [ Exit ] A :=
    fun s => (inr (inl x), s).

  (** * Comparisons *)
  Definition lt {A : Type} {R} `{OrderDec A R} (x y : A) : bool :=
    match compare x y with
    | Eq => false
    | Lt => true
    | Gt => false
    end.

  Definition gt {A : Type} {R} `{OrderDec A R} (x y : A) : bool :=
    match compare x y with
    | Eq => false
    | Lt => false
    | Gt => true
    end.

  Definition le {A : Type} {R} `{OrderDec A R} (x y : A) : bool :=
    match compare x y with
    | Eq => true
    | Lt => true
    | Gt => false
    end.

  Definition ge {A : Type} {R} `{OrderDec A R} (x y : A) : bool :=
    match compare x y with
    | Eq => true
    | Lt => false
    | Gt => true
    end.

  Definition min {A : Type} {R} `{OrderDec A R} (x y : A) : A :=
    match compare x y with
    | Eq => x
    | Lt => x
    | Gt => y
    end.

  Definition max {A : Type} {R} `{OrderDec A R} (x y : A) : A :=
    match compare x y with
    | Eq => x
    | Lt => y
    | Gt => x
    end.

  Definition compare {A : Type} {R} `{OrderDec A R} (x y : A) : Z :=
    match compare x y with
    | Eq => 0
    | Lt => -1
    | Gt => 1
    end.

  (** * Boolean operations *)

  (** * Composition operators *)
  Definition reverse_apply {A B : Type} (x : A) (f : A -> B) : B :=
    f x.

  (** * Integer arithmetic *)

  (** * Bitwise operations *)

  (** * Floating-point arithmetic *)
  (* TODO *)

  (** * String operations *)

  (** * Character operations *)
  Definition int_of_char (c : ascii) : Z :=
    Z.of_nat (nat_of_ascii c).

  Definition char_of_int (n : Z) : M [ Invalid_argument ] ascii :=
    if andb (le 0 n) (le n 255) then
      ret (ascii_of_nat (Z.to_nat n))
    else
      raise_Invalid_argument "char_of_int".

  (** * Unit operations *)
  Definition ignore {A : Type} (_ : A) : unit :=
    tt.

  (** * String conversion functions *)
  Definition string_of_bool (b : bool) : string :=
    if b then
      "true" % string
    else
      "false" % string.

  (* TODO *)
  Definition bool_of_string (s : string) : bool :=
    false.

  (* TODO *)
  Definition string_of_int (n : Z) : string :=
    "0" % string.

  (* TODO *)
  Definition int_of_string (s : string) : Z :=
    0.

  (** * Pair operations *)

  (** * List operations *)
  (** The concatenation of lists with an implicit parameter. *)
  Definition app {A : Type} (l1 l2 : list A) : list A :=
    app l1 l2.

  (** * Input/output *)
  (* TODO: add channels. *)

  (** * Output functions on standard output *)
  Definition print_string (message : string) : M [IO] unit :=
    fun s =>
      match s with
      | ((stream_i, stream_o), _) =>
        (inl tt, ((stream_i, message :: stream_o), tt))
      end.

  Definition print_char (c : ascii) : M [IO] unit :=
    print_string (String.String c String.EmptyString).

  Definition print_int (n : Z) : M [IO] unit :=
    print_string (string_of_int n).

  Definition print_newline (_ : unit) : M [IO] unit :=
    print_char "010" % char.

  Definition print_endline (message : string) : M [IO] unit :=
    let! _ := print_string message in
    print_newline tt.

  (** * Output functions on standard error *)
  (* TODO: do it on the error channel. *)
  Definition prerr_string (message : string) : M [IO] unit :=
    print_string message.

  Definition prerr_char (c : ascii) : M [IO] unit :=
    print_char c.

  Definition prerr_int (n : Z) : M [IO] unit :=
    print_int n.

  Definition prerr_newline (_ : unit) : M [IO] unit :=
    print_newline tt.

  Definition prerr_endline (message : string) : M [IO] unit :=
    print_endline message.

  (** * Input functions on standard input *)
  Definition read_line (_ : unit) : M [IO] string :=
    fun s =>
      match s with
      | ((stream_i, stream_o), _) =>
        match stream_i with
        | FiniteStream.nil _ =>
          (inl "" % string, s) (* We could raise an [End_of_file] exception. *)
        | FiniteStream.cons message stream_i =>
          (inl message, ((stream_i, stream_o), tt))
        end
      end.

  Definition read_int (_ : unit) : M [IO] Z :=
    let! s := read_line tt in
    ret (int_of_string s).

  (** * General output functions *)
  (* TODO *)

  (** * General input functions *)
  (* TODO *)

  (** * Operations on large files *)
  (* TODO *)

  (** * References *)
  Definition ref {A : Type} (x : A)
    : M [ OCaml.Effect.State.state A ] (OCaml.Effect.State.t A) :=
    OCaml.Effect.State.ref x.

  (** * Operations on format strings *)
  (* TODO *)

  (** * Program termination *)
  (* TODO *)
End Pervasives.

(*Module List.
  Definition length {A : Type} (l : list A) : Z :=
    Z_of_nat (length l).

  Definition hd {A : Type} (l : list A) : M [Failure] A :=
    match l with
    | [] => raise_Failure "hd" % string
    | x :: _ => ret x
    end.

  Definition tl {A : Type} (l : list A) : M [Failure] (list A) :=
    match l with
    | [] => raise_Failure "tl" % string
    | _ :: l => ret l
    end.

  Definition nth {A : Type} (l : list A) (n : Z) : M [Failure; Invalid_argument] A :=
    if n <? 0 then
      lift [_;_] "01" (raise_Invalid_argument "List.nth" % string)
    else
      lift [_;_] "10" (
        let n := Z.to_nat n in
        match List.nth_error l n with
        | None => raise_Failure "nth" % string
        | Some x => ret x
        end).

  Fixpoint flatten {A : Type} (ll : list (list A)) : list A :=
    match ll with
    | [] => []
    | l :: ll => l ++ flatten ll
    end.

  (** * Iterators *)
  Fixpoint mapi_aux {A B : Type} (f : Z -> A -> B) (l : list A) (n : nat) : list B :=
    match l with
    | [] => []
    | x :: l => f (Z.of_nat n) x :: mapi_aux f l (S n)
    end.

  Definition mapi {A B : Type} (f : Z -> A -> B) (l : list A) : list B :=
    mapi_aux f l O.

  Fixpoint rev_map_aux {A B : Type} (f : A -> B) (l : list A) (r : list B) : list B :=
    match l with
    | [] => r
    | x :: l => rev_map_aux f l (f x :: r)
    end.

  Definition rev_map {A B : Type} (f : A -> B) (l : list A) : list B :=
    rev_map_aux f l [].

  Definition fold_left {A B : Type} (f : A -> B -> A) (a : A) (l : list B) : A :=
    List.fold_left f l a.

  Definition fold_right {A B : Type} (f : A -> B -> B) (l : list A) (a : B) : B :=
    List.fold_right f a l.

  (** * Iterators on two lists *)
  Fixpoint map2 {A B C : Type} (f : A -> B -> C) (l1 : list A) (l2 : list B)
    : M [Invalid_argument] (list C) :=
    match (l1, l2) with
    | ([], []) => ret []
    | (x1 :: l1, x2 :: l2) =>
      let! l := map2 f l1 l2 in
      ret (f x1 x2 :: l)
    | _ => raise_Invalid_argument "map2"
    end.

  Fixpoint rev_map2_aux {A B C : Type} (f : A -> B -> C) (l1 : list A) (l2 : list B)
    (r : list C) : M [Invalid_argument] (list C) :=
    match (l1, l2) with
    | ([], []) => ret r
    | (x1 :: l1, x2 :: l2) => rev_map2_aux f l1 l2 (f x1 x2 :: r)
    | _ => raise_Invalid_argument "rev_map2"
    end.

  Definition rev_map2 {A B C : Type} (f : A -> B -> C) (l1 : list A) (l2 : list B)
    : M [Invalid_argument] (list C) :=
    rev_map2_aux f l1 l2 [].

  Fixpoint fold_left2 {A B C : Type} (f : A -> B -> C -> A) (a : A)
    (l1 : list B) (l2 : list C) : M [Invalid_argument] A :=
    match (l1 , l2) with
    | ([], []) => ret a
    | (x1 :: l1, x2 :: l2) => fold_left2 f (f a x1 x2) l1 l2
    | _ => raise_Invalid_argument "fold_left2"
    end.

  Fixpoint fold_right2 {A B C : Type} (f : A -> B -> C -> C)
    (l1 : list A) (l2 : list B) (a : C) :  M [Invalid_argument] C :=
    match (l1, l2) with
    | ([], []) => ret a
    | (x1 :: l1, x2 :: l2) =>
      let! a := fold_right2 f l1 l2 a in
      ret (f x1 x2 a)
    | _ => raise_Invalid_argument "fold_right2"
    end.

  (** * List scanning *)
  (** * List searching *)
  (** * Association lists *)
  (** * Lists of pairs *)
  (** * Sorting *)
End List.*)

Module String.
  Definition length (s : string) : Z :=
    Z.of_nat (String.length s).

  (* TODO: raise an exception if n < 0. *)
  Definition get (s : string) (n : Z) : ascii :=
    match String.get (Z.to_nat n) s with
    | None => "?" % char
    | Some c => c
    end.

  Fixpoint _make (n : nat) (c : ascii) : string :=
    match n with
    | O => EmptyString
    | S n => String c (_make n c)
    end.

  (* TODO: raise an exception if n < 0. *)
  Definition make (n : Z) (c : ascii) : string :=
    _make (Z.to_nat n) c.

  (* TODO *)
  Definition sub (s : string) (start : Z) (length : Z) : string :=
    s.

  (* TODO *)
  Definition escaped (s : string) : string :=
    s.
End String.
