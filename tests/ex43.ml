(** While loops *)
let slow_div (a : int) (b : int) : int =
  let y = ref 0 in
  let c = ref 0 in
  while (!y + b <= a) do
    y := !y + b;
    c := !c + 1
  done;
  !c

let nested () =
  let a = ref [ref [1; 2]; ref [3; 4; 5]; ref [6; 7]] in
  let b = ref [] in
  while List.length !a > 0 do
    match !a with
    | [] -> ()
    | x :: a' ->
      while List.length !x > 0 do
        match !x with
        | [] -> ()
        | y :: x' ->
          b := y :: !b;
          x := x'
      done;
      a := a'
  done;
  !b

let raises (b : bool) : unit =
  while b do
    failwith "b is true"
  done

let complex_raises (b : bool) : unit =
  let f a = (a, 15, failwith "b is true") in
  while b do
    f true
  done

let argument_effects (x : int ref) (y : int) =
  let y = ref y in
  let z = ref 0 in
  let i = ref 0 in
  while !i <= !x do
    let j = ref 0 in
    while !j <= !y do
      z := !z + 1;
      j := !j + 1
    done;
    y := !y - 1;
    i := !i + 1
  done;
  !z
