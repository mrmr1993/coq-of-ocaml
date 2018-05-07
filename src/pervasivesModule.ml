(** The initially opened module. *)
open FullEnvi
open Effect.Type
open SmartPrint

let rec find_interfaces_dir (base : string) : string option =
  let base_path = Filename.dirname base in
  if base == base_path then
    None
  else
    let interfaces_dir = Filename.concat base_path "interfaces" in
    if Sys.file_exists interfaces_dir && Sys.is_directory interfaces_dir then
      Some interfaces_dir
    else
      find_interfaces_dir base_path

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
  FullEnvi.empty
  (* Values specific to the translation to Coq *)
  |> add_typ [] "nat"
  |> add_constructor [] "O"
  |> add_constructor [] "S"
  |> add_typ [] "sum"
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
  |> add_typ [] "Z"
  |> add_typ [] "ascii"
  |> add_typ [] "string"
  |> add_typ [] "bool"
  |> add_constructor [] "false"
  |> add_constructor [] "true"
  |> add_typ [] "unit"
  |> add_constructor [] "tt"
  |> add_typ [] "list"
  |> add_constructor [] "[]"
  |> add_constructor [] "cons"
  |> add_typ [] "option"
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
  (* Operations on format strings *)
  (* Program termination *)

  (* List *)
  |> enter_module
  |> leave_module "OCaml" Effect.Type.leave_prefix
  |> fun env -> begin
       match find_interfaces_dir Sys.executable_name with
       | Some interface_dir ->
         FullEnvi.add_wrapped_mod (Interface.to_wrapped_mod "OCaml"
           (Interface.of_file (Filename.concat interface_dir "list.interface"))
           env) env
       | None ->
         prerr_endline @@ to_string 80 2 (!^ "Warning: interfaces directory was not found");
         env end
  |> enter_module
  |> open_module' ["OCaml"]
  (* |> fun env -> SmartPrint.to_stdout 80 2 (FullEnvi.pp env); env *)

let env : unit FullEnvi.t = FullEnvi.map (fun _ -> ()) env_with_effects
