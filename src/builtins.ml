let _nat = BoundName.of_name [] "nat"
let _O = BoundName.of_name [] "O"
let _S = BoundName.of_name [] "S"
let _sum = BoundName.of_name [] "sum"
let _inl = BoundName.of_name [] "inl"
let _inr = BoundName.of_name [] "inr"
let _Counter = BoundName.of_name [] "Counter"
let _read_counter = BoundName.of_name [] "read_counter"
let _NonTermination = BoundName.of_name [] "NonTermination"
let _not_terminated = BoundName.of_name [] "not_terminated"
let _for_to = BoundName.of_name ["OCaml"; "Basics"] "for_to"
let _for_downto = BoundName.of_name ["OCaml"; "Basics"] "for_downto"

let _Z = BoundName.of_name [] "Z"
let _ascii = BoundName.of_name [] "ascii"
let _string = BoundName.of_name [] "string"
let _bool = BoundName.of_name [] "bool"
let _unit = BoundName.of_name [] "unit"
let _tt = BoundName.of_name [] "tt"
let _list = BoundName.of_name [] "list"

let _assert = BoundName.of_name ["OCaml"] "assert"

let _exception = BoundName.of_name ["OCaml"] "exception"
let _exn = BoundName.of_name ["OCaml"] "exn"
let _Match_failure = BoundName.of_name ["OCaml"] "Match_failure"
let _match_failure = BoundName.of_name ["OCaml"] "match_failure"
let _assert_failure = BoundName.of_name ["OCaml"] "assert_failure"
let _invalid_argument = BoundName.of_name ["OCaml"] "invalid_argument"
let _failure = BoundName.of_name ["OCaml"] "failure"

let _raise = BoundName.of_name ["OCaml"; "Pervasives"] "raise"

module Localize = struct
  let _nat env = FullEnvi.localize env _nat
  let _O env = FullEnvi.localize env _O
  let _S env = FullEnvi.localize env _S
  let _sum env = FullEnvi.localize env _sum
  let _inl env = FullEnvi.localize env _inl
  let _inr env = FullEnvi.localize env _inr
  let _Counter env = FullEnvi.localize env _Counter
  let _read_counter env = FullEnvi.localize env _read_counter
  let _NonTermination env = FullEnvi.localize env _NonTermination
  let _not_terminated env = FullEnvi.localize env _not_terminated
  let _for_to env = FullEnvi.localize env _for_to
  let _for_downto env = FullEnvi.localize env _for_downto

  let _Z env = FullEnvi.localize env _Z
  let _ascii env = FullEnvi.localize env _ascii
  let _string env = FullEnvi.localize env _string
  let _bool env = FullEnvi.localize env _bool
  let _unit env = FullEnvi.localize env _unit
  let _tt env = FullEnvi.localize env _tt
  let _list env = FullEnvi.localize env _list

  let _assert env = FullEnvi.localize env _assert

  let _exception env = FullEnvi.localize env _exception
  let _exn env = FullEnvi.localize env _exn
  let _Match_failure env = FullEnvi.localize env _Match_failure
  let _match_failure env = FullEnvi.localize env _match_failure
  let _assert_failure env = FullEnvi.localize env _assert_failure
  let _invalid_argument env = FullEnvi.localize env _invalid_argument
  let _failure env = FullEnvi.localize env _failure

  let _raise env = FullEnvi.localize env _raise
end
