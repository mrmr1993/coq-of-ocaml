Require Import Libraries.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition sum_assoc_left (A B C : Type) (x : A + (B + C)) : (A + B) + C :=
  match x with
  | inl x => inl (inl x)
  | inr (inl x) => inl (inr x)
  | inr (inr x) => inr x
  end.

Module Effect.
  Record t := make {
    S : Type;
    E : Type }.

  Definition nil : t := {|
    S := unit;
    E := Empty_set |}.

  Definition add (e1 e2 : t) : t := {|
    S := S e1 * S e2;
    E := E e1 + E e2 |}.

  Fixpoint of_list (es : list t) : t :=
    match es with
    | [] => nil
    | e :: es => add e (of_list es)
    end.

  Definition state (es : list t) : Type :=
    S (of_list es).

  Definition error (es : list t) : Type :=
    E (of_list es).

  Module Ebs.
    Fixpoint domain (ebs : list (t * bool)) : list t :=
      match ebs with
      | [] => []
      | (e, _) :: ebs => e :: domain ebs
      end.

    Fixpoint sub (ebs : list (t * bool)) : list t :=
      match ebs with
      | [] => []
      | (_, false) :: ebs => sub ebs
      | (e, true) :: ebs => e :: sub ebs
      end.

    Fixpoint filter_state (ebs : list (t * bool)) (s : state (domain ebs))
      {struct ebs} : state (sub ebs).
      destruct ebs as [|[e b] ebs].
      - exact s.
      - destruct b; simpl in *.
        + exact (fst s, filter_state ebs (snd s)).
        + exact (filter_state ebs (snd s)).
    Defined.

    Fixpoint expand_exception (ebs : list (t * bool))
      (err : error (sub ebs)) {struct ebs}
      : error (domain ebs).
      destruct ebs as [|[e b] ebs].
      - exact err.
      - destruct b; simpl in *.
        + exact (match err with
          | inl err => inl err
          | inr err => inr (expand_exception ebs err)
          end).
        + exact (inr (expand_exception ebs err)).
    Defined.

    Fixpoint expand_state (ebs : list (t * bool))
      (s1 : state (sub ebs)) (s2 : state (domain ebs))
      {struct ebs} : state (domain ebs).
      destruct ebs as [|[e b] ebs].
      - exact s1.
      - destruct b; simpl in *.
        + exact (fst s1, expand_state ebs (snd s1) (snd s2)).
        + exact (fst s2, expand_state ebs s1 (snd s2)).
    Defined.
  End Ebs.

  Module Lens.
    Fixpoint get_state (n : nat) (es : list t) {struct es}
      : state es -> S (List.nth n es Effect.nil).
      destruct es as [ | e es];
        destruct n as [ | n].
      - exact (fun _ => tt).
      - exact (fun _ => tt).
      - destruct 1 as [s ss].
        exact s.
      - destruct 1 as [s ss].
        exact (get_state n es ss).
    Defined.

    Fixpoint set_state (n : nat) (es : list t) {struct es}
      : S (List.nth n es Effect.nil) -> state es -> state es.
      destruct es as [ | e es].
      - exact (fun _ ss => ss).
      - destruct n as [ | n].
        * exact (fun s ss => (s, snd ss)).
        * exact (fun s ss => (fst ss, set_state n es s (snd ss))).
    Defined.

    Fixpoint set_error (n : nat) (es : list t) {struct es}
      : E (List.nth n es Effect.nil) -> error es.
      destruct es as [ | e es].
      - destruct n; destruct 1.
      - destruct n as [ | n].
        * exact (fun e => inl e).
        * exact (fun e => inr (set_error n es e)).
    Defined.
  End Lens.
End Effect.

Module Raw.
  Definition M (es : list Effect.t) (A : Type) : Type :=
    Effect.state es -> (A + Effect.error es) * Effect.state es.

  Definition ret {es : list Effect.t} {A : Type} (x : A) : M es A :=
    fun s => (inl x, s).

  Definition bind {es : list Effect.t} {A B : Type}
    (x : M es A) (f : A -> M es B) : M es B :=
    fun s =>
      let (x, s) := x s in
      match x with
      | inl x => f x s
      | inr e => (inr e, s)
      end.

  Definition lift {A : Type} (es : list Effect.t) (bs : string)
    (x : M _ A) : M _ A :=
    let aux (ebs : list (Effect.t * bool)) (x : M (Effect.Ebs.sub ebs) A)
      : M (Effect.Ebs.domain ebs) A :=
      fun s =>
        let (r, s') := x (Effect.Ebs.filter_state ebs s) in
        let s := Effect.Ebs.expand_state ebs s' s in
        match r with
        | inl x => (inl x, s)
        | inr err => (inr (Effect.Ebs.expand_exception ebs err), s)
        end in
    let fix bool_list (s : string) : list bool :=
      match s with
      | EmptyString => []
      | String "0" s => false :: bool_list s
      | String _ s => true :: bool_list s
      end in
    aux (List.combine es (bool_list bs)) x.
End Raw.

Definition M (es : list Effect.t) (A : Type) : Type :=
  match es with
  | [] => A
  | _ => Effect.state es -> (A + Effect.error es) * Effect.state es
  end.

Definition of_raw {es : list Effect.t} {A : Type} : Raw.M es A -> M es A :=
  match es with
  | [] => fun x =>
    match x tt with
    | (inl x, _) => x
    | (inr err, _) => match err with end
    end
  | _ => fun x => x
  end.

Definition to_raw {es : list Effect.t} {A : Type} : M es A -> Raw.M es A :=
  match es with
  | [] => fun x => fun tt => (inl x, tt)
  | _ => fun x => x
  end.

Definition ret {es : list Effect.t} {A : Type} (x : A) : M es A :=
  of_raw (Raw.ret x).

Definition bind {es : list Effect.t} {A B : Type}
  (x : M es A) (f : A -> M es B) : M es B :=
  of_raw (Raw.bind (to_raw x) (fun x => to_raw (f x))).

Notation "'let!' X ':=' A 'in' B" := (bind A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).

Definition lift {A : Type} (es : list Effect.t) (bs : string)
  (x : M _ A) : M _ A :=
  of_raw (Raw.lift es bs (to_raw x)).

Module Exception.
  Fixpoint remove_nth (es : list Effect.t) (n : nat) : list Effect.t :=
    match es with
    | [] => []
    | e :: es =>
      match n with
      | O => es
      | S n => e :: remove_nth es n
      end
    end.

  Definition nth_is_stateless (es : list Effect.t) (n : nat) : Type :=
    match List.nth_error es n with
    | Some e => Effect.S e
    | None => unit
    end.

  Fixpoint input (es : list Effect.t) (n : nat) (tt' : nth_is_stateless es n)
    (s : Effect.state (remove_nth es n)) {struct es} : Effect.state es.
    destruct es as [|e es].
    - exact s.
    - destruct n as [|n].
      + exact (tt', s).
      + refine (fst s, input es n tt' (snd s)).
  Defined.

  Fixpoint output (es : list Effect.t) (n : nat) (s : Effect.state es)
    {struct es} : Effect.state (remove_nth es n).
    destruct es as [|e es].
    - exact s.
    - destruct n as [|n].
      + exact (snd s).
      + exact (fst s, output _ _ (snd s)).
  Defined.

  Fixpoint error (es : list Effect.t) (n : nat) (err : Effect.error es)
    {struct es}
    : Effect.E (nth n es Effect.nil) + Effect.error (remove_nth es n).
    destruct es as [|e es].
    - destruct err.
    - destruct n as [|n].
      + exact err.
      + refine (
          match err with
          | inl err => inr (inl err)
          | inr err =>
            match error _ _ err with
            | inl err => inl err
            | inr err => inr (inr err)
            end
          end).
  Defined.

  Definition run {A : Type} {es : list Effect.t} (n : nat)
    (x : M es A) (tt' : nth_is_stateless es n)
    : M (remove_nth es n) (A + Effect.E (List.nth n es Effect.nil)) :=
    of_raw (fun s =>
      let (r, s) := (to_raw x) (input _ _ tt' s) in
      (match r with
      | inl x => inl (inl x)
      | inr err => sum_assoc_left (inr (error _ _ err))
      end, output _ _ s)).
End Exception.

Module Run.
  Fixpoint remove_nth (es : list Effect.t) (n : nat) : list Effect.t :=
    match es with
    | [] => []
    | e :: es =>
      match n with
      | O => es
      | S n => e :: remove_nth es n
      end
    end.

  Fixpoint input (es : list Effect.t) (n : nat)
    (s : Effect.S (List.nth n es Effect.nil))
    (ss : Effect.state (remove_nth es n)) {struct es} : Effect.state es.
    destruct es as [|e es].
    - exact ss.
    - destruct n as [|n].
      + exact (s, ss).
      + refine (fst ss, input es n s (snd ss)).
  Defined.

  Fixpoint output (es : list Effect.t) (n : nat) (ss : Effect.state es)
    {struct es}
    : Effect.S (List.nth n es Effect.nil) * Effect.state (remove_nth es n).
    destruct es as [|e es].
    - destruct n; exact (tt, ss).
    - destruct n as [|n].
      + exact (fst ss, snd ss).
      + exact (
        let (s, ss') := output _ _ (snd ss) in
        (s, (fst ss, ss'))).
  Defined.

  Fixpoint error (es : list Effect.t) (n : nat) (err : Effect.error es)
    {struct es}
    : Effect.E (nth n es Effect.nil) + Effect.error (remove_nth es n).
    destruct es as [|e es].
    - destruct err.
    - destruct n as [|n].
      + exact err.
      + refine (
          match err with
          | inl err => inr (inl err)
          | inr err =>
            match error _ _ err with
            | inl err => inl err
            | inr err => inr (inr err)
            end
          end).
  Defined.

  Definition run {A : Type} {es : list Effect.t} (n : nat) (x : M es A)
    : let S := Effect.S (List.nth n es Effect.nil) in
      let E := Effect.E (List.nth n es Effect.nil) in
      S -> M (remove_nth es n) ((A + E) * S) :=
    fun s => of_raw (fun ss =>
      let (r, ss) := (to_raw x) (input _ _ s ss) in
      let (s, ss) := output es n ss in
      (match r with
      | inl x => inl (inl x, s)
      | inr err =>
        match error es n err with
        | inl e => inl (inr e, s)
        | inr ee => inr ee
        end
      end, ss)).

  (** Expected value for [tt']: [tt]. *)
  Definition exception {A : Type} {es : list Effect.t} (n : nat) (x : M es A)
    (tt' : Effect.S (List.nth n es Effect.nil))
    : M (remove_nth es n) (A + Effect.E (List.nth n es Effect.nil)) :=
    let! x := run n x tt' in
    ret (fst x).

  (** Expected value for [error_is_empty]: [fun err => match err with end]. *)
  Definition reader {A : Type} {es : list Effect.t} (n : nat) (x : M es A)
    (error_is_empty : Effect.E (List.nth n es Effect.nil) -> False)
    : Effect.S (List.nth n es Effect.nil) -> M (remove_nth es n) A :=
    fun s =>
      let! x := run n x s in
      match fst x with
      | inl x => ret x
      | inr err => False_rect _ (error_is_empty err)
      end.
End Run.

Module Union.
  Open Scope nat.

  Definition INPUT (es_in es_out : list Effect.t) : Type :=
    forall (n : nat), Effect.S (List.nth n es_out Effect.nil) ->
      Effect.state es_in -> Effect.state es_in.

  Definition OUTPUT (es_in es_out : list Effect.t) : Type :=
    forall (n : nat), Effect.state es_in ->
      Effect.S (List.nth n es_out Effect.nil).

  Definition ERROR (es_in es_out : list Effect.t) : Type :=
    forall (n : nat), Effect.E (List.nth n es_out Effect.nil) ->
      Effect.error es_in.

  Definition CORRECT (es_in es_out : list Effect.t)
    (index_map : list nat) :=
    List.map (fun n => List.nth n es_in Effect.nil) index_map = es_out.

  Definition IN_RANGE (es_in es_out : list Effect.t)
    (index_map : list nat) :=
    let l := length es_in in
    List.map (fun x => S x - l) index_map =
    List.map (fun _ => 0) index_map.

  (** Describes a union of effects.
      [index_map] describes how to get each effect in [es_out] from an
      effect in [es_in]. This allows aliases for the same effects to
      appear multiple times in [es_out], backed by a single effect in
      [es_in], so that effects containing type variables can resolve to
      the same effect as necessary.

      This has a few quirks:
      - The input and output effect lists need to be parameters to
        make typechecking work correctly. This means that code using
        it must provide a parameter for [es_in], which will be inferred
        at the callsite.
      - There are two proofs to make typechecking work: [index_correct]
        and [index_in_range]. To keep these both as unintrusive as
        possible, they are both equality proofs, so passing [eq_refl]
        should be enough.
      - The [input], [output], and [error] functions only discharge a
        single effect from the union. This means that all low-level
        functions *MUST* only use a single unionable effect or manually
        perform the discharges as necessary.
   *)
  Record t (es_in es_out : list Effect.t) := {
    index_map : list nat;
    index_correct : CORRECT es_in es_out index_map;
    index_in_range : IN_RANGE es_in es_out index_map;
    input : INPUT es_in es_out;
    output : OUTPUT es_in es_out;
    error : ERROR es_in es_out
  }.

  (** Caution: All code using this assumes that it is the first effect
      in the effects list. *)
  Definition union (es_in es_out : list Effect.t) : Effect.t :=
    Effect.add
      (Effect.make (t es_in es_out) Empty_set)
      (Effect.of_list es_in).

  Fixpoint length_compare {A : Type} (n : nat) (l : list A) {struct l} :
    {n < length l} + {length l <= n}.
    destruct l as [ | x l], n as [ | n].
    - now right.
    - right.
      rewrite (plus_n_O (S n)); now apply le_plus_r.
    - left.
      apply (lt_plus_trans 0 1 (length l)); now repeat constructor.
    - destruct (length_compare _ n l) as [Sn_lt | Sn_ge].
      * left; now apply lt_n_S.
      * right; now apply le_n_S.
  Defined.

  Definition base_input (es_in es_out : list Effect.t)
    : forall (index_map : list nat),
        CORRECT es_in es_out index_map -> INPUT es_in es_out.
    unfold CORRECT, INPUT.
    intros index_map index_correct n s.
    destruct (length_compare n es_out) as [lt_len | ge_len].
    - apply (Effect.Lens.set_state (List.nth n index_map 0)).
      rewrite <- (List.map_nth (fun n => nth n es_in Effect.nil)).
      rewrite index_correct.
      now rewrite (nth_indep _ _ Effect.nil).
    - exact (fun state => state).
  Defined.

  Definition base_output (es_in es_out : list Effect.t)
    : forall (index_map : list nat),
        CORRECT es_in es_out index_map -> OUTPUT es_in es_out.
    unfold CORRECT, INPUT.
    intros index_map index_correct n ss.
    destruct (length_compare n es_out) as [lt_len | ge_len].
    - erewrite (List.nth_indep _ _ _); [ | assumption ].
      rewrite <- index_correct.
      erewrite (List.map_nth (fun n => nth n es_in Effect.nil) index_map _ n).
      now apply (Effect.Lens.get_state (List.nth n index_map 0)).
    - now rewrite List.nth_overflow.
  Defined.

  Definition base_error (es_in es_out : list Effect.t)
    : forall (index_map : list nat),
        CORRECT es_in es_out index_map -> ERROR es_in es_out.
    unfold CORRECT, ERROR.
    intros index_map index_correct n.
    destruct (length_compare n es_out) as [lt_len | ge_len].
    - erewrite List.nth_indep; [ | assumption ].
      rewrite <- index_correct.
      erewrite (List.map_nth (fun n => nth n es_in Effect.nil) index_map _ n).
      now apply (Effect.Lens.set_error (List.nth n index_map 0)).
    - now rewrite List.nth_overflow.
  Defined.

  Definition create (es_in es_out : list Effect.t) (index_map : list nat)
    (correct : CORRECT es_in es_out index_map)
    (in_range : IN_RANGE es_in es_out index_map) : t es_in es_out := {|
    index_map := index_map;
    index_correct := correct;
    index_in_range := in_range;
    input := base_input correct;
    output := base_output correct;
    error := base_error correct
  |}.

  Definition compose_input (es_in es_mid es_out : list Effect.t)
    : forall (index_map : list nat),
        CORRECT es_mid es_out index_map ->
        INPUT es_in es_mid -> INPUT es_in es_out.
    unfold CORRECT, INPUT.
    intros index_map index_correct input1 n s.
    destruct (length_compare n es_out) as [lt_len | ge_len].
    - apply (input1 (List.nth n index_map 0)).
      rewrite <- (List.map_nth (fun n => nth n es_mid Effect.nil)).
      rewrite index_correct.
      now rewrite (nth_indep _ _ Effect.nil).
    - exact (fun state => state).
  Defined.

  Definition compose_output (es_in es_mid es_out : list Effect.t)
    : forall (index_map : list nat),
        CORRECT es_mid es_out index_map ->
        OUTPUT es_in es_mid -> OUTPUT es_in es_out.
    unfold CORRECT, OUTPUT.
    intros index_map index_correct output1 n.
    destruct (length_compare n es_out) as [lt_len | ge_len].
    - erewrite (List.nth_indep _ _ _); [ | assumption ].
      rewrite <- index_correct.
      erewrite (List.map_nth (fun n => nth n es_mid Effect.nil) index_map _ n).
      now apply (output1 (List.nth n index_map 0)).
    - now rewrite List.nth_overflow.
  Defined.

  Definition compose_error (es_in es_mid es_out : list Effect.t)
    : forall (index_map : list nat),
        CORRECT es_mid es_out index_map ->
        ERROR es_in es_mid -> ERROR es_in es_out.
    unfold CORRECT, ERROR.
    intros index_map index_correct error1 n.
    destruct (length_compare n es_out) as [lt_len | ge_len].
    - erewrite List.nth_indep; [ | assumption ].
      rewrite <- index_correct.
      erewrite (List.map_nth (fun n => nth n es_mid Effect.nil) index_map _ n).
      now apply (error1 (List.nth n index_map 0)).
    - now rewrite List.nth_overflow.
  Defined.

  Lemma in_range_equiv
    : forall (index_map : list nat) (es_in es_out : list Effect.t),
        IN_RANGE es_in es_out index_map <->
        List.Forall (fun n => n < length es_in) index_map.
  Proof.
    unfold IN_RANGE.
    intros index_map es_in _.
    induction index_map as [ | x index_map IH].
    - easy.
    - destruct es_in as [ | e es_in].
        split; now inversion 1.
      split; simpl.
      * inversion 1 as [[x_sub_eq_0 tl_range]].
        rewrite x_sub_eq_0 in tl_range.
        now firstorder.
      * inversion 1 as [ | n l x_le_len tl_forall].
        apply IH in tl_forall.
        f_equal; [ | now firstorder ].
        revert x_le_len; clear.
        generalize (List.length es_in) as m; clear.
        induction x as [ | x IH];
        [ | intros [ | m] Sx_le ].
        + easy.
        + inversion Sx_le as [ | n SSx_le_O].
          now inversion SSx_le_O.
        + now apply IH, le_S_n.
  Qed.

  Lemma compose_correct (es_in es_mid es_out : list Effect.t)
    : forall (index_map1 index_map2 : list nat),
        CORRECT es_mid es_out index_map1 ->
        CORRECT es_in es_mid index_map2 ->
        IN_RANGE es_mid es_out index_map1 ->
        IN_RANGE es_in es_mid index_map2 ->
        CORRECT es_in es_out
          (List.map (fun n => List.nth n index_map2 0) index_map1).
  Proof.
    unfold CORRECT, IN_RANGE.
    intros index_map1.
    revert es_out.
    induction index_map1 as [ | i index_map1 IH];
      intros es_out index_map2 correct1 correct2 range1 range2.
    - now rewrite <- correct1.
    - rewrite <- correct1, <- correct2.
      simpl; f_equal.
      * erewrite (List.nth_indep (map _ _)).
        + now rewrite map_nth.
        + apply (in_range_equiv _ _ es_out) in range1.
          inversion range1.
          now rewrite correct2.
      * destruct es_out as [ | e es_out];
          inversion correct1 as [[e_eq es_out_eq]].
        specialize (IH es_out index_map2 es_out_eq correct2).
        rewrite correct2, es_out_eq.
        apply IH.
        + now inversion range1.
        + now inversion range2.
  Qed.

  Lemma compose_in_range (es_in es_mid es_out : list Effect.t)
    : forall (index_map1 index_map2 : list nat),
        CORRECT es_mid es_out index_map1 ->
        CORRECT es_in es_mid index_map2 ->
        IN_RANGE es_mid es_out index_map1 ->
        IN_RANGE es_in es_mid index_map2 ->
        IN_RANGE es_in es_out
          (List.map (fun n => List.nth n index_map2 0) index_map1).
  Proof.
    unfold CORRECT, IN_RANGE.
    intros index_map1.
    revert es_out.
    induction index_map1 as [ | i index_map1 IH];
      intros es_out index_map2 correct1 correct2 range1 range2.
      easy.
    destruct es_in as [ | ei es_in];
    [ | destruct es_out as [ | eo es_out] ].
    - destruct index_map2 as [ | i2 index_map2].
        simpl in *; rewrite <- correct2 in range1; now inversion range1.
        now inversion range2.
    - now inversion correct1.
    - simpl; f_equal.
      * apply (in_range_equiv _ _ es_out) in range1.
        inversion range1 as [ | i' index_map1' i_lt_len _].
        cut (In (nth i index_map2 0) index_map2).
        + intros in_index_map2.
          apply (List.in_map (fun x => S x - List.length (ei :: es_in)))
            in in_index_map2.
          rewrite range2 in in_index_map2.
          apply List.in_map_iff in in_index_map2.
          now destruct in_index_map2 as [_ [eq_0 _]].
        + apply List.nth_In.
          replace (List.length index_map2) with (List.length es_mid).
            assumption.
          rewrite <- correct2.
          now apply List.map_length.
      * now apply (IH es_out);
        [ inversion correct1 | | inversion range1 | ].
  Qed.

  Definition compose {es_in es_mid es_out : list Effect.t}
    (map1 : t es_in es_mid) (map2 : t es_mid es_out)
    : t es_in es_out :=
    {|
      index_map := List.map (fun n => List.nth n (index_map map1) 0)
        (index_map map2);
      index_correct := compose_correct
        (index_correct map2) (index_correct map1)
        (index_in_range map2) (index_in_range map1);
      index_in_range := compose_in_range
        (index_correct map2) (index_correct map1)
        (index_in_range map2) (index_in_range map1);
      input := compose_input (index_correct map2) (input map1);
      output := compose_output (index_correct map2) (output map1);
      error := compose_error (index_correct map2) (error map1)
    |}.

  Definition mix {es_in es_mid es_out es : list Effect.t}
    {A : Type} (map : t es_mid es_out)
    (x : M (union es_in es_out :: es) A)
    : M (union es_in es_mid :: es) A :=
    fun s =>
      let (union_state, s) := s in
      let (map', s_inner) := union_state in
      let s := ((compose map' map, s_inner), s) in
      let (x, s) := x s in
      let (union_state, s) := s in
      let s := ((map', snd union_state), s) in
      (x, s).

  Definition lift {es_in es_out es : list Effect.t} {A : Type}
    (n : nat) (x : M (nth n es_out Effect.nil :: es) A)
    : M (union es_in es_out :: es) A :=
    fun s =>
      let (union_state, s) := s in
      let (map, s_inner) := union_state in
      let s' := output map n s_inner in
      let s := (s', s) in
      let (x, s) := x s in
      let (s', s) := s in
      let s_inner := input map n s' s_inner in
      let s := ((map, s_inner), s) in
      let x := match x with
        | inl x => inl x
        | inr (inl e) => inr (inl (inr (error map n e)))
        | inr (inr e) => inr (inr e)
        end in
      (x, s).

  Close Scope nat.
End Union.

Module State.
  Unset Implicit Arguments.

  Record t (A : Type) := {pos : nat; default_value : A}.

  Arguments pos {A} _.
  Arguments default_value {A} _.

  Fixpoint replace (n : nat) {A : Type} (v : A) (l : list A) : list A :=
    match n, l with
    | O, [] => [v]
    | O, a :: l' => v :: l'
    | S _, [] => []
    | S n', a :: l' => a :: replace n' v l'
    end.

  Definition position {A : Type} (x : t A) (l : list A) : nat :=
    Lists.List.length l - S (pos x).

  Definition state (A : Type) : Effect.t :=
    Effect.make (list A) Empty_set.

  Definition peek {A B : Type}
    (mval : (A + Effect.error [state B]) * Effect.state [state B])
    : A * list B :=
    match mval with
    | (inl x, (l, _)) => (x, l)
    | (inr (inl x), _) => Empty_set_rect _ x
    | (inr (inr x), _) => Empty_set_rect _ x
    end.

  Definition write {A : Type} (x : t A) (value : A)
    : M [ state A ] unit :=
    fun s => (inl tt, (replace (position x (fst s)) value (fst s), tt)).

  Definition read {A : Type} (x : t A) : M [ state A ] A :=
    fun s => (inl (Lists.List.nth (position x (fst s)) (fst s) (default_value x)), s).

  Definition ref {A : Type} (x : A) : M [ state A ] (t A) :=
    fun s => let l := fst s in
      (inl {|
          pos := Lists.List.length l;
          default_value := x
        |}, (x :: l, tt)).

  Definition init {A : Type} (x : A) : t A :=
    {| pos := 0; default_value := x |}.

  Definition peekstate {A : Type} (x : unit) : M [ state A ] (list A) :=
    fun s => (inl (fst s), s).

  Definition global {A : Type} (x : t A) (l : list A)
    : M [ state nat] (t A) :=
    fun s =>
      let n := match fst s with | [n] => n | _ => length l end in
      (inl {| pos := n; default_value := default_value x |}, ([n], tt)).

  Set Implicit Arguments.
End State.

(** A stream which may be finite. *)
Module FiniteStream.
  CoInductive t (A : Type) : Type :=
  | nil : t A
  | cons : A -> t A -> t A.
End FiniteStream.

Definition IO := Effect.make (FiniteStream.t string * list string) Empty_set.

Definition Counter := Effect.make nat Empty_set.

Definition NonTermination := Effect.make unit unit.

Definition read_counter (_ : unit) : M [Counter] nat :=
  fun s => (inl (fst s), s).

Definition not_terminated {A : Type} (_ : unit) : M [NonTermination] A :=
  fun s => (inr (inl tt), s).
