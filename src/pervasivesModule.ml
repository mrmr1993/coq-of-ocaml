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
  let typ_d (x : int) : Effect.Descriptor.t =
    let i = string_of_int x in
    Effect.Descriptor.singleton
      (Effect.Descriptor.Id.Type (Effect.PureType.Variable i))
      { BoundName.depth = 0; BoundName.path_name =
        (PathName.of_name ["OCaml"; "Effect"; "State"] "state") } in
  let add_exn path base =
    add_exception_with_effects path base
      (Effect.Descriptor.Id.Ether (PathName.of_name path base)) in
  FullEnvi.empty None (fun _ -> failwith "No modules loaded")
  (* Values specific to the translation to Coq *)
  |> Typ.add [] "nat" Pure
  |> Constructor.add [] "O"
  |> Constructor.add [] "S"
  |> Typ.add [] "sum" Pure
  |> Constructor.add [] "inl"
  |> Constructor.add [] "inr"
  |> Descriptor.add [] "IO"
  |> Descriptor.add [] "Counter"
  |> Var.add [] "read_counter" (Arrow (d [[], "Counter"], Pure))
  |> Descriptor.add [] "NonTermination"
  |> Var.add [] "not_terminated" (Arrow (d [[], "NonTermination"], Pure))
  |> Var.add ["OCaml"] "assert" (Arrow (d [["OCaml"], "Assert_failure"], Pure))

  (* The core library *)
  (* Built-in types *)
  |> Typ.add [] "Z" Pure
  |> Typ.add [] "ascii" Pure
  |> Typ.add [] "string" Pure
  |> Typ.add [] "bool" Pure
  |> Constructor.add [] "false"
  |> Constructor.add [] "true"
  |> Typ.add [] "unit" Pure
  |> Constructor.add [] "tt"
  |> Typ.add [] "list" Pure
  |> Constructor.add [] "[]"
  |> Constructor.add [] "cons"
  |> Typ.add [] "option" Pure
  |> Constructor.add [] "None"
  |> Constructor.add [] "Some"
  (* Predefined exceptions *)
  |> Typ.add ["OCaml"] "exn" Pure
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
  |> Descriptor.add ["OCaml"; "Effect"; "State"] "state"
  |> Typ.add ["OCaml"; "Effect"; "State"] "t" (Arrow (d [["OCaml"; "Effect"; "State"], "state"], Pure))
  |> Var.add ["OCaml"; "Effect"; "State"] "peekstate" Pure
  |> Var.add ["OCaml"; "Effect"; "State"] "global" Pure
  |> Var.add ["OCaml"; "Effect"; "State"] "read" (Arrow (typ_d 0, Pure))
  |> Var.add ["OCaml"; "Effect"; "State"] "write" (Arrow (d [], Arrow (typ_d 0, Pure)))

  (* Pervasives *)
  (* Exceptions *)
  |> Var.add ["OCaml"; "Pervasives"] "invalid_arg" (Arrow (d [["OCaml"], "Invalid_argument"], Pure))
  |> Var.add ["OCaml"; "Pervasives"] "failwith" (Arrow (d [["OCaml"], "Failure"], Pure))
  |> add_exn ["OCaml"; "Pervasives"] "Exit"
  (* Comparisons *)
  |> Var.add [] "equiv_decb" Pure
  |> Var.add [] "nequiv_decb" Pure
  |> Var.add ["OCaml"; "Pervasives"] "lt" Pure
  |> Var.add ["OCaml"; "Pervasives"] "gt" Pure
  |> Var.add ["OCaml"; "Pervasives"] "le" Pure
  |> Var.add ["OCaml"; "Pervasives"] "ge" Pure
  |> Var.add ["OCaml"; "Pervasives"] "compare" Pure
  |> Var.add ["OCaml"; "Pervasives"] "min" Pure
  |> Var.add ["OCaml"; "Pervasives"] "max" Pure
  (* Boolean operations *)
  |> Var.add [] "negb" Pure
  |> Var.add [] "andb" Pure
  |> Var.add [] "orb" Pure
  (* Composition operators *)
  |> Var.add ["OCaml"; "Pervasives"] "reverse_apply" Pure
  |> Var.add [] "apply" Pure
  (* Integer arithmetic *)
  |> Var.add ["Z"] "opp" Pure
  |> Var.add [] "" Pure
  |> Var.add ["Z"] "succ" Pure
  |> Var.add ["Z"] "pred" Pure
  |> Var.add ["Z"] "add" Pure
  |> Var.add ["Z"] "sub" Pure
  |> Var.add ["Z"] "mul" Pure
  |> Var.add ["Z"] "div" Pure
  |> Var.add ["Z"] "modulo" Pure
  |> Var.add ["Z"] "abs" Pure
  (* Bitwise operations *)
  |> Var.add ["Z"] "land" Pure
  |> Var.add ["Z"] "lor" Pure
  |> Var.add ["Z"] "lxor" Pure
  |> Var.add ["Z"] "shiftl" Pure
  |> Var.add ["Z"] "shiftr" Pure
  (* Floating-point arithmetic *)
  (* String operations *)
  |> Var.add ["String"] "append" Pure
  (* Character operations *)
  |> Var.add ["OCaml"; "Pervasives"] "int_of_char" Pure
  |> Var.add ["OCaml"; "Pervasives"] "char_of_int" (Arrow (d [["OCaml"], "Invalid_argument"], Pure))
  (* Unit operations *)
  |> Var.add ["OCaml"; "Pervasives"] "ignore" Pure
  (* String conversion functions *)
  |> Var.add ["OCaml"; "Pervasives"] "string_of_bool" Pure
  |> Var.add ["OCaml"; "Pervasives"] "bool_of_string" Pure
  |> Var.add ["OCaml"; "Pervasives"] "string_of_int" Pure
  |> Var.add ["OCaml"; "Pervasives"] "int_of_string" Pure
  (* Pair operations *)
  |> Var.add [] "fst" Pure
  |> Var.add [] "snd" Pure
  (* List operations *)
  |> Var.add ["OCaml"; "Pervasives"] "app" Pure
  (* Input/output *)
  (* Output functions on standard output *)
  |> Var.add ["OCaml"; "Pervasives"] "print_char" (Arrow (d [[], "IO"], Pure))
  |> Var.add ["OCaml"; "Pervasives"] "print_string" (Arrow (d [[], "IO"], Pure))
  |> Var.add ["OCaml"; "Pervasives"] "print_int" (Arrow (d [[], "IO"], Pure))
  |> Var.add ["OCaml"; "Pervasives"] "print_endline" (Arrow (d [[], "IO"], Pure))
  |> Var.add ["OCaml"; "Pervasives"] "print_newline" (Arrow (d [[], "IO"], Pure))
  (* Output functions on standard error *)
  |> Var.add ["OCaml"; "Pervasives"] "prerr_char" (Arrow (d [[], "IO"], Pure))
  |> Var.add ["OCaml"; "Pervasives"] "prerr_string" (Arrow (d [[], "IO"], Pure))
  |> Var.add ["OCaml"; "Pervasives"] "prerr_int" (Arrow (d [[], "IO"], Pure))
  |> Var.add ["OCaml"; "Pervasives"] "prerr_endline" (Arrow (d [[], "IO"], Pure))
  |> Var.add ["OCaml"; "Pervasives"] "prerr_newline" (Arrow (d [[], "IO"], Pure))
  (* Input functions on standard input *)
  |> Var.add ["OCaml"; "Pervasives"] "read_line" (Arrow (d [[], "IO"], Pure))
  |> Var.add ["OCaml"; "Pervasives"] "read_int" (Arrow (d [[], "IO"], Pure))
  (* General output functions *)
  (* General input functions *)
  (* Operations on large files *)
  (* References *)
  |> Var.add ["OCaml"; "Pervasives"] "ref" Pure
  (* Operations on format strings *)
  (* Program termination *)

  (* List *)
  |> enter_module (CoqName.Name "OCaml")
  |> leave_module Effect.Type.leave_prefix Effect.Type.resolve_open
  |> fun env ->
       let lazy_loader = ref LazyLoader.empty in
       let get_module mod_name =
         let (wmod, loader) = LazyLoader.find_mod_opt env !lazy_loader mod_name in
         lazy_loader := loader;
         wmod in
       {env with get_module}
  |> enter_section
  |> open_module' Loc.Unknown ["OCaml"]

let show out_channel : unit =
  to_out_channel 80 2 out_channel (FullEnvi.pp env_with_effects)

(* show stdout;; *)

let env : unit FullEnvi.t = FullEnvi.map (fun _ -> ()) env_with_effects
