(** The initially opened module. *)
open FullEnvi
open Effect.Type
open SmartPrint

let env_with_effects : Effect.Type.t FullEnvi.t =
  let descriptor (path, base) =
    let x = PathName.of_name path base in
    Effect.Descriptor.singleton (Effect.Descriptor.Id.Ether x)
      { BoundName.path_name = x; depth = 0 } in
  let d xs : Effect.Descriptor.t =
    Effect.Descriptor.union (List.map descriptor xs) in
  let add_exn path base =
    add_exception_with_effects path base
      (Effect.Descriptor.Id.Ether (PathName.of_name path base)) in
  FullEnvi.empty (fun _ -> failwith "No modules loaded")
  (* Values specific to the translation to Coq *)
  |> add_typ [] "nat" Pure
  |> add_constructor [] "O"
  |> add_constructor [] "S"
  |> add_typ [] "sum" Pure
  |> add_constructor [] "inl"
  |> add_constructor [] "inr"
  |> add_descriptor [] "IO"
  |> add_descriptor [] "Counter"
  |> add_var [] "read_counter" (Arrow (d [[], "Counter"], Pure))
  |> add_descriptor [] "NonTermination"
  |> add_var [] "not_terminated" (Arrow (d [[], "NonTermination"], Pure))
  |> add_var ["OCaml"] "assert" (Arrow (d [["OCaml"], "Assert_failure"], Pure))

  (* The core library *)
  (* Built-in types *)
  |> add_typ [] "Z" Pure
  |> add_typ [] "ascii" Pure
  |> add_typ [] "string" Pure
  |> add_typ [] "bool" Pure
  |> add_constructor [] "false"
  |> add_constructor [] "true"
  |> add_typ [] "unit" Pure
  |> add_constructor [] "tt"
  |> add_typ [] "list" Pure
  |> add_constructor [] "[]"
  |> add_constructor [] "cons"
  |> add_typ [] "option" Pure
  |> add_constructor [] "None"
  |> add_constructor [] "Some"
  (* Predefined exceptions *)
  |> add_exn ["OCaml"] "Match_failure"
  |> add_exn ["OCaml"] "Assert_failure"
  |> add_exn ["OCaml"] "Invalid_argument"
  |> add_exn ["OCaml"] "Failure"
  |> add_exn ["OCaml"] "Not_found"
  |> add_exn ["OCaml"] "Out_of_memory"
  |> add_exn ["OCaml"] "Stack_overflow"
  |> add_exn ["OCaml"] "Sys_error"
  |> add_exn ["OCaml"] "End_of_file"
  |> add_exn ["OCaml"] "Division_by_zero"
  |> add_exn ["OCaml"] "Sys_blocked_io"
  |> add_exn ["OCaml"] "Undefined_recursive_module"
  (* State *)
  |> add_typ ["OCaml"; "Effect"; "State"] "t" Pure
  |> add_descriptor ["OCaml"; "Effect"; "State"] "state"
  |> add_var ["OCaml"; "Effect"; "State"] "read" (Arrow (d [["OCaml"; "Effect"; "State"], "state"], Pure))
  |> add_var ["OCaml"; "Effect"; "State"] "write" (Arrow (d [], Arrow (d [["OCaml"; "Effect"; "State"], "state"], Pure)))

  (* Pervasives *)
  (* Exceptions *)
  |> add_var ["OCaml"; "Pervasives"] "invalid_arg" (Arrow (d [["OCaml"], "Invalid_argument"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "failwith" (Arrow (d [["OCaml"], "Failure"], Pure))
  |> add_exn ["OCaml"; "Pervasives"] "Exit"
  (* Comparisons *)
  |> add_var [] "equiv_decb" Pure
  |> add_var [] "nequiv_decb" Pure
  |> add_var ["OCaml"; "Pervasives"] "lt" Pure
  |> add_var ["OCaml"; "Pervasives"] "gt" Pure
  |> add_var ["OCaml"; "Pervasives"] "le" Pure
  |> add_var ["OCaml"; "Pervasives"] "ge" Pure
  |> add_var ["OCaml"; "Pervasives"] "compare" Pure
  |> add_var ["OCaml"; "Pervasives"] "min" Pure
  |> add_var ["OCaml"; "Pervasives"] "max" Pure
  (* Boolean operations *)
  |> add_var [] "negb" Pure
  |> add_var [] "andb" Pure
  |> add_var [] "orb" Pure
  (* Composition operators *)
  |> add_var ["OCaml"; "Pervasives"] "reverse_apply" Pure
  |> add_var [] "apply" Pure
  (* Integer arithmetic *)
  |> add_var ["Z"] "opp" Pure
  |> add_var [] "" Pure
  |> add_var ["Z"] "succ" Pure
  |> add_var ["Z"] "pred" Pure
  |> add_var ["Z"] "add" Pure
  |> add_var ["Z"] "sub" Pure
  |> add_var ["Z"] "mul" Pure
  |> add_var ["Z"] "div" Pure
  |> add_var ["Z"] "modulo" Pure
  |> add_var ["Z"] "abs" Pure
  (* Bitwise operations *)
  |> add_var ["Z"] "land" Pure
  |> add_var ["Z"] "lor" Pure
  |> add_var ["Z"] "lxor" Pure
  |> add_var ["Z"] "shiftl" Pure
  |> add_var ["Z"] "shiftr" Pure
  (* Floating-point arithmetic *)
  (* String operations *)
  |> add_var ["String"] "append" Pure
  (* Character operations *)
  |> add_var ["OCaml"; "Pervasives"] "int_of_char" Pure
  |> add_var ["OCaml"; "Pervasives"] "char_of_int" (Arrow (d [["OCaml"], "Invalid_argument"], Pure))
  (* Unit operations *)
  |> add_var ["OCaml"; "Pervasives"] "ignore" Pure
  (* String conversion functions *)
  |> add_var ["OCaml"; "Pervasives"] "string_of_bool" Pure
  |> add_var ["OCaml"; "Pervasives"] "bool_of_string" Pure
  |> add_var ["OCaml"; "Pervasives"] "string_of_int" Pure
  |> add_var ["OCaml"; "Pervasives"] "int_of_string" Pure
  (* Pair operations *)
  |> add_var [] "fst" Pure
  |> add_var [] "snd" Pure
  (* List operations *)
  |> add_var ["OCaml"; "Pervasives"] "app" Pure
  (* Input/output *)
  (* Output functions on standard output *)
  |> add_var ["OCaml"; "Pervasives"] "print_char" (Arrow (d [[], "IO"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "print_string" (Arrow (d [[], "IO"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "print_int" (Arrow (d [[], "IO"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "print_endline" (Arrow (d [[], "IO"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "print_newline" (Arrow (d [[], "IO"], Pure))
  (* Output functions on standard error *)
  |> add_var ["OCaml"; "Pervasives"] "prerr_char" (Arrow (d [[], "IO"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "prerr_string" (Arrow (d [[], "IO"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "prerr_int" (Arrow (d [[], "IO"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "prerr_endline" (Arrow (d [[], "IO"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "prerr_newline" (Arrow (d [[], "IO"], Pure))
  (* Input functions on standard input *)
  |> add_var ["OCaml"; "Pervasives"] "read_line" (Arrow (d [[], "IO"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "read_int" (Arrow (d [[], "IO"], Pure))
  (* General output functions *)
  (* General input functions *)
  (* Operations on large files *)
  (* References *)
  |> add_var ["OCaml"; "Pervasives"] "ref" (Arrow (d [["OCaml"; "Effect"; "State"], "state"], Pure))
  (* Operations on format strings *)
  (* Program termination *)

  (* List *)
  |> enter_module
  |> leave_module "OCaml" Effect.Type.leave_prefix
  |> fun env ->
       let lazy_loader = ref LazyLoader.empty in
       let get_module mod_name =
         let (wmod, loader) = LazyLoader.find_wrapped_mod_opt env !lazy_loader mod_name in
         lazy_loader := loader;
         wmod in
       {env with get_module}
  |> enter_module
  |> open_module' Loc.Unknown ["OCaml"]

let show out_channel : unit =
  to_out_channel 80 2 out_channel (FullEnvi.pp env_with_effects)

(* show stdout;; *)

let env : unit FullEnvi.t = FullEnvi.map (fun _ -> ()) env_with_effects
