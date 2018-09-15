(** For loops *)
let x (a : int) (b : int) =
  let y = ref 0 in
  for i = a to b do
    y := !y + 1
  done;
  !y

let nested (x : int) (y : int) =
  let a = ref [] in
  for i = 0 to x do
    for j = 0 to y do
      a := true :: !a
    done;
    a := false :: !a
  done;
  !a

let raises (x : int) =
  for i = 0 to x do
    failwith "x is not less than 0"
  done

let argument_effects (x : int ref) (y : int) =
  let y = ref y in
  let z = ref 0 in
  for i = 0 to !x do
    for j = 0 to !y do
      z := !z + 1
    done;
    y := !y - 1
  done;
  !z
