Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Require OCaml.List.

Definition get_local_ref (tt : unit) : M [ Effect.State.state Z ] Z :=
  let! x := Pervasives.ref 12 in
  Effect.State.read x.

Definition set_local_ref (tt : unit) : M [ Effect.State.state Z ] Z :=
  let! x := Pervasives.ref 12 in
  let! _ := Effect.State.write x 15 in
  Effect.State.read x.

Definition add_multiple_by_refs (a : Z) (b : Z) (c : Z) (d : Z)
  : M [ Effect.State.state Z ] Z :=
  let! x := Pervasives.ref a in
  let! _ :=
    let! x_1 :=
      let! x_1 := Effect.State.read x in
      ret (Z.add x_1 b) in
    Effect.State.write x x_1 in
  let! y := Pervasives.ref c in
  let! _ :=
    let! x_1 :=
      let! x_1 := Effect.State.read y in
      ret (Z.add x_1 d) in
    Effect.State.write y x_1 in
  let! z :=
    let! x_1 :=
      let! x_1 := Effect.State.read x in
      let! x_2 := Effect.State.read y in
      ret (Z.add x_1 x_2) in
    Pervasives.ref x_1 in
  Effect.State.read z.

Definition set_ref (x : Effect.State.t Z) : M [ Effect.State.state Z ] unit :=
  Effect.State.write x 15.

Definition get_ref (x : Effect.State.t Z) : M [ Effect.State.state Z ] Z :=
  Effect.State.read x.

Definition update_ref (x : Effect.State.t Z)
  : M [ Effect.State.state Z ] unit :=
  let! x_1 :=
    let! x_1 := Effect.State.read x in
    ret (Z.add x_1 5) in
  Effect.State.write x x_1.

Definition new_ref (x : unit) : M [ Effect.State.state Z ] (Effect.State.t Z) :=
  Pervasives.ref 15.

Definition r_state := OCaml.Effect.State.global_state.
Definition r : M [ OCaml.Effect.State.state Z; r_state ]
  (OCaml.Effect.State.t Z) := OCaml.Effect.State.global 18.

Definition set_r (x : unit) : M [ Effect.State.state Z; r_state ] unit :=
  let! x_1 := r in
  lift [_;_] "10" (set_ref x_1).

Definition get_r (x : unit) : M [ Effect.State.state Z; r_state ] Z :=
  let! x_1 := r in
  lift [_;_] "10" (get_ref x_1).

Definition r_add_15 (x : unit) : M [ Effect.State.state Z; r_state ] Z :=
  let! i := get_r tt in
  let! _ := set_r tt in
  let! j := get_r tt in
  let! _ :=
    let! x_1 := r in
    lift [_;_] "10" (Effect.State.write x_1 (Z.add i j)) in
  let! x_1 := r in
  lift [_;_] "10" (Effect.State.read x_1).

Definition mixed_type {es_in : list Effect.t} (x : unit)
  : M
    [
      OCaml.Effect.Union.union es_in
        [
          (Effect.State.state Z);
          (Effect.State.state bool);
          (Effect.State.state string)
        ];
      r_state
    ] (bool * string * Z) :=
  let! b := lift [_;_] "10" (@Union.lift _ _ _ [_;_;_] 1 (Pervasives.ref true))
    in
  let! str :=
    lift [_;_] "10" (@Union.lift _ _ _ [_;_;_] 2 (Pervasives.ref "" % string))
    in
  let update (x_1 : unit)
    : M
      [
        OCaml.Effect.Union.union _
          [ (Effect.State.state bool); (Effect.State.state string) ]
      ] unit :=
    match x_1 with
    | tt =>
      let! _ :=
        @Union.lift _ _ _ [_;_] 0
          (let! x_2 := Effect.State.read b in
          Effect.State.write b x_2) in
      @Union.lift _ _ _ [_;_] 1
        (let! x_2 :=
          let! x_2 := Effect.State.read str in
          ret (String.append "toggle " % string x_2) in
        Effect.State.write str x_2)
    end in
  let! _ :=
    lift [_;_] "10"
      (@Union.mix _ _ _ _ [_;_;_] [1;2]%nat eq_refl eq_refl (update tt)) in
  let! _ :=
    lift [_;_] "10"
      (@Union.mix _ _ _ _ [_;_;_] [1;2]%nat eq_refl eq_refl (update tt)) in
  let! _ :=
    lift [_;_] "10"
      (@Union.mix _ _ _ _ [_;_;_] [1;2]%nat eq_refl eq_refl (update tt)) in
  let! x_1 :=
    lift [_;_] "10" (@Union.lift _ _ _ [_;_;_] 1 (Effect.State.read b)) in
  let! x_2 :=
    lift [_;_] "10" (@Union.lift _ _ _ [_;_;_] 2 (Effect.State.read str)) in
  let! x_3 :=
    @Union.lift _ _ _ [_;_;_] 0
      (let! x_3 := r in
      lift [_;_] "10" (Effect.State.read x_3)) in
  ret (x_1, x_2, x_3).

Definition partials_test {es_in : list Effect.t} (x : unit)
  : M
    [
      OCaml.Effect.Union.union es_in
        [ (Effect.State.state Z); (Effect.State.state (list Z)) ];
      r_state
    ] (Effect.State.t Z) :=
  match x with
  | tt =>
    let f1 (x : Effect.State.t Z) (y : Z)
      : M [ Effect.State.state Z ] (Effect.State.t Z) :=
      let! _ := Effect.State.write x y in
      ret x in
    let! f1_test :=
      @Union.lift _ _ _ [_;_] 0
        (let! x_1 := r in
        ret (f1 x_1)) in
    lift [_;_] "10"
      (let! f1_test := @Union.lift _ _ _ [_;_] 0 (f1_test 15) in
      let f2 (l1 : Effect.State.t (list Z)) (l2 : list string)
        : M
          [
            OCaml.Effect.Union.union _
              [ (Effect.State.state Z); (Effect.State.state (list Z)) ]
          ] (Effect.State.t Z) :=
        let! x_1 :=
          @Union.lift _ _ _ [_;_] 1
            (let! x_1 :=
              let! x_1 := Effect.State.read l1 in
              ret (List.length x_1) in
            ret (Z.add x_1 (List.length l2))) in
        @Union.lift _ _ _ [_;_] 0 (Pervasives.ref x_1) in
      let! f2_test :=
        @Union.lift _ _ _ [_;_] 1
          (let! x_1 := Pervasives.ref (cons 1 (cons 2 (cons 3 []))) in
          ret (f2 x_1)) in
      let! f2_test := f2_test (cons "hi" % string (cons "hey" % string [])) in
      @Union.lift _ _ _ [_;_] 0
        (let! x_1 := Effect.State.read f1_test in
        f1 f2_test x_1))
  end.

Definition multiple_returns_test (x : unit)
  : M [ Effect.State.state Z ] (Z * (Effect.State.t Z)) :=
  match x with
  | tt =>
    let f (x : Effect.State.t Z) (y : Z)
      : M [ Effect.State.state Z ]
        (Z ->
          M [ Effect.State.state Z ]
            ((Effect.State.t Z) -> M [ Effect.State.state Z ] (Effect.State.t Z))) :=
      let! _ := Effect.State.write x y in
      ret
        (fun z =>
          let! _ :=
            let! x_1 :=
              let! x_1 := Effect.State.read x in
              ret (Z.add x_1 z) in
            Effect.State.write x x_1 in
          ret
            (fun w =>
              let! tmp := Effect.State.read w in
              let! _ :=
                let! x_1 :=
                  let! x_1 := Effect.State.read x in
                  ret (Z.mul 2 x_1) in
                Effect.State.write w x_1 in
              let! _ := Effect.State.write x tmp in
              ret x)) in
    let! s := Pervasives.ref 110 in
    let! f1 :=
      let! x_1 := Pervasives.ref 5 in
      ret (f x_1) in
    let! f2 := f1 2 in
    let! f3 := f2 7 in
    let! f4 := f3 s in
    let! x_1 := Effect.State.read f4 in
    ret (x_1, s)
  end.

Definition type_vars_test {A B : Type} {es_in : list Effect.t}
  (x : Effect.State.t A) (y : Effect.State.t B) (a : A) (b : B)
  : M
    [
      OCaml.Effect.Union.union es_in
        [ (Effect.State.state A); (Effect.State.state B) ]
    ] unit :=
  let! _ := @Union.lift _ _ _ [_;_] 0 (Effect.State.write x a) in
  @Union.lift _ _ _ [_;_] 1 (Effect.State.write y b).

Definition resolves_test1 {A : Type} (x : Effect.State.t A) (a : A) (b : A)
  : M [ Effect.State.state A ] unit := Union.inject 2 (type_vars_test x x a b).

Definition resolves_test2 {A : Type} {es_in : list Effect.t}
  (x : Effect.State.t Z) (y : Effect.State.t A) (a : Z) (b : A)
  : M
    [
      OCaml.Effect.Union.union es_in
        [ (Effect.State.state A); (Effect.State.state Z) ]
    ] unit :=
  @Union.mix _ _ _ _ [_;_] [1;0]%nat eq_refl eq_refl (type_vars_test x y a b).

Definition resolves_test3
  (x : Effect.State.t Z) (y : Effect.State.t Z) (a : Z) (b : Z)
  : M [ Effect.State.state Z ] unit := Union.inject 2 (type_vars_test x y a b).
