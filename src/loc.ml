open SmartPrint

type t =
  | Unknown
  | Known of Lexing.position * Lexing.position

let pp (l : t) : SmartPrint.t =
  match l with
  | Unknown -> !^ "?"
  | Known (start, _) ->
    let (_, line, _) = Location.get_pos_info start in
    OCaml.int line

let to_user (l : t) : SmartPrint.t =
  match l with
  | Unknown -> !^ "?"
  | Known (start, _) ->
    let (file_name, line, _) = Location.get_pos_info start in
    !^ file_name ^-^ !^ "," ^^ !^ "line" ^^ OCaml.int line

let to_tuple (l : t) : string * int * int =
  match l with
  | Unknown -> ("", 0, 0)
  | Known (start, _) -> Location.get_pos_info start

let of_location (l : Location.t) : t =
  Known (l.Location.loc_start, l.Location.loc_end)
