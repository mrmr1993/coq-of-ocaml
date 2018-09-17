Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Require OCaml.List.

Definition slow_div (a : Z) (b : Z)
  : M [ OCaml.Effect.State.state Z; Counter; NonTermination ] Z :=
  let! y := lift [_;_;_] "100" (OCaml.Pervasives.ref 0) in
  let! c := lift [_;_;_] "100" (OCaml.Pervasives.ref 0) in
  let! _ :=
    let fix while (counter : nat)
      : M [ OCaml.Effect.State.state Z; NonTermination ] unit :=
      match counter with
      | O => lift [_;_] "01" (not_terminated tt)
      | S counter =>
        let! check :=
          lift [_;_] "10"
            (let! x :=
              let! x := OCaml.Effect.State.read y in
              ret (Z.add x b) in
            ret (OCaml.Pervasives.le x a)) in
        if check then
          let! _ :=
            lift [_;_] "10"
              (let! _ :=
                let! x :=
                  let! x := OCaml.Effect.State.read y in
                  ret (Z.add x b) in
                OCaml.Effect.State.write y x in
              let! x :=
                let! x := OCaml.Effect.State.read c in
                ret (Z.add x 1) in
              OCaml.Effect.State.write c x) in
          while counter
        else
          ret tt
      end in
    let! counter := lift [_;_;_] "010" (read_counter tt) in
    lift [_;_;_] "101" (while counter) in
  lift [_;_;_] "100" (OCaml.Effect.State.read c).

Definition nested {es_in : list Effect.t} (x : unit)
  : M
    [
      OCaml.Effect.Union.union es_in
        [
          (OCaml.Effect.State.state (list Z));
          (OCaml.Effect.State.state (list (OCaml.Effect.State.t (list Z))))
        ];
      Counter;
      NonTermination
    ] (list Z) :=
  match x with
  | tt =>
    let! a :=
      lift [_;_;_] "100"
        (let! x_1 :=
          @Union.lift _ _ _ [_;_] 0
            (let! x_1 := OCaml.Pervasives.ref (cons 1 (cons 2 [])) in
            let! x_2 :=
              let! x_2 := OCaml.Pervasives.ref (cons 3 (cons 4 (cons 5 []))) in
              let! x_3 :=
                let! x_3 := OCaml.Pervasives.ref (cons 6 (cons 7 [])) in
                ret (cons x_3 []) in
              ret (cons x_2 x_3) in
            ret (cons x_1 x_2)) in
        @Union.lift _ _ _ [_;_] 1 (OCaml.Pervasives.ref x_1)) in
    let! b :=
      lift [_;_;_] "100" (@Union.lift _ _ _ [_;_] 0 (OCaml.Pervasives.ref []))
      in
    let! _ :=
      let fix while (counter : nat)
        : M
          [
            OCaml.Effect.Union.union _
              [
                (OCaml.Effect.State.state (list Z));
                (OCaml.Effect.State.state
                  (list
                    (OCaml.Effect.State.t
                      (list
                        Z))))
              ];
            Counter;
            NonTermination
          ] unit :=
        match counter with
        | O => lift [_;_;_] "001" (not_terminated tt)
        | S counter =>
          let! check :=
            lift [_;_;_] "100"
              (@Union.lift _ _ _ [_;_] 1
                (let! x_1 :=
                  let! x_1 := OCaml.Effect.State.read a in
                  ret (OCaml.List.length x_1) in
                ret (OCaml.Pervasives.gt x_1 0))) in
          if check then
            let! _ :=
              let! x_1 :=
                lift [_;_;_] "100"
                  (@Union.lift _ _ _ [_;_] 1 (OCaml.Effect.State.read a)) in
              match x_1 with
              | [] => ret tt
              | cons x a' =>
                let! _ :=
                  @Union.lift _ _ _ [_;_] 0
                    (let fix while_1 (counter_1 : nat)
                      : M [ OCaml.Effect.State.state (list Z); NonTermination ]
                        unit :=
                      match counter_1 with
                      | O => lift [_;_] "01" (not_terminated tt)
                      | S counter_1 =>
                        let! check_1 :=
                          lift [_;_] "10"
                            (let! x_1 :=
                              let! x_1 := OCaml.Effect.State.read x in
                              ret (OCaml.List.length x_1) in
                            ret (OCaml.Pervasives.gt x_1 0)) in
                        if check_1 then
                          let! _ :=
                            lift [_;_] "10"
                              (let! x_1 := OCaml.Effect.State.read x in
                              match x_1 with
                              | [] => ret tt
                              | cons y x' =>
                                let! _ :=
                                  let! x_1 :=
                                    let! x_1 := OCaml.Effect.State.read b in
                                    ret (cons y x_1) in
                                  OCaml.Effect.State.write b x_1 in
                                OCaml.Effect.State.write x x'
                              end) in
                          while_1 counter_1
                        else
                          ret tt
                      end in
                    let! counter_1 := lift [_;_;_] "010" (read_counter tt) in
                    lift [_;_;_] "101" (while_1 counter_1)) in
                lift [_;_;_] "100"
                  (@Union.lift _ _ _ [_;_] 1 (OCaml.Effect.State.write a a'))
              end in
            while counter
          else
            ret tt
        end in
      let! counter := lift [_;_;_] "010" (read_counter tt) in
      while counter in
    lift [_;_;_] "100" (@Union.lift _ _ _ [_;_] 0 (OCaml.Effect.State.read b))
  end.

Definition raises (b : bool)
  : M [ Counter; NonTermination; OCaml.Failure ] unit :=
  let fix while (counter : nat) : M [ NonTermination; OCaml.Failure ] unit :=
    match counter with
    | O => lift [_;_] "10" (not_terminated tt)
    | S counter =>
      let check := b in
      if check then
        let! _ :=
          lift [_;_] "01"
            ((OCaml.Pervasives.failwith "b is true" % string) :
              M [ OCaml.Failure ] unit) in
        while counter
      else
        ret tt
    end in
  let! counter := lift [_;_;_] "100" (read_counter tt) in
  lift [_;_;_] "011" (while counter).

Definition complex_raises (b : bool)
  : M [ Counter; NonTermination; OCaml.Failure ] unit :=
  let f {A B : Type} (a : A) : M [ OCaml.Failure ] (A * Z * B) :=
    let! x := OCaml.Pervasives.failwith "b is true" % string in
    ret (a, 15, x) in
  let fix while (counter : nat) : M [ NonTermination; OCaml.Failure ] unit :=
    match counter with
    | O => lift [_;_] "10" (not_terminated tt)
    | S counter =>
      let check := b in
      if check then
        let! _ :=
          lift [_;_] "01" ((f true) : M [ OCaml.Failure ] (bool * Z * unit)) in
        while counter
      else
        ret tt
    end in
  let! counter := lift [_;_;_] "100" (read_counter tt) in
  lift [_;_;_] "011" (while counter).

Definition argument_effects (x : OCaml.Effect.State.t Z) (y : Z)
  : M [ OCaml.Effect.State.state Z; Counter; NonTermination ] Z :=
  let! y := lift [_;_;_] "100" (OCaml.Pervasives.ref y) in
  let! z := lift [_;_;_] "100" (OCaml.Pervasives.ref 0) in
  let! i := lift [_;_;_] "100" (OCaml.Pervasives.ref 0) in
  let! _ :=
    let fix while (counter : nat)
      : M [ OCaml.Effect.State.state Z; Counter; NonTermination ] unit :=
      match counter with
      | O => lift [_;_;_] "001" (not_terminated tt)
      | S counter =>
        let! check :=
          lift [_;_;_] "100"
            (let! x_1 := OCaml.Effect.State.read i in
            let! x_2 := OCaml.Effect.State.read x in
            ret (OCaml.Pervasives.le x_1 x_2)) in
        if check then
          let! _ :=
            let! j := lift [_;_;_] "100" (OCaml.Pervasives.ref 0) in
            let! _ :=
              let fix while_1 (counter_1 : nat)
                : M [ OCaml.Effect.State.state Z; NonTermination ] unit :=
                match counter_1 with
                | O => lift [_;_] "01" (not_terminated tt)
                | S counter_1 =>
                  let! check_1 :=
                    lift [_;_] "10"
                      (let! x_1 := OCaml.Effect.State.read j in
                      let! x_2 := OCaml.Effect.State.read y in
                      ret (OCaml.Pervasives.le x_1 x_2)) in
                  if check_1 then
                    let! _ :=
                      lift [_;_] "10"
                        (let! _ :=
                          let! x_1 :=
                            let! x_1 := OCaml.Effect.State.read z in
                            ret (Z.add x_1 1) in
                          OCaml.Effect.State.write z x_1 in
                        let! x_1 :=
                          let! x_1 := OCaml.Effect.State.read j in
                          ret (Z.add x_1 1) in
                        OCaml.Effect.State.write j x_1) in
                    while_1 counter_1
                  else
                    ret tt
                end in
              let! counter_1 := lift [_;_;_] "010" (read_counter tt) in
              lift [_;_;_] "101" (while_1 counter_1) in
            lift [_;_;_] "100"
              (let! _ :=
                let! x_1 :=
                  let! x_1 := OCaml.Effect.State.read y in
                  ret (Z.sub x_1 1) in
                OCaml.Effect.State.write y x_1 in
              let! x_1 :=
                let! x_1 := OCaml.Effect.State.read i in
                ret (Z.add x_1 1) in
              OCaml.Effect.State.write i x_1) in
          while counter
        else
          ret tt
      end in
    let! counter := lift [_;_;_] "010" (read_counter tt) in
    while counter in
  lift [_;_;_] "100" (OCaml.Effect.State.read z).