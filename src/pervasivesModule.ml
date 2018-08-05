(** The initially opened module. *)
open FullEnvi
open Effect.Type
open SmartPrint

let env_with_effects : Effect.Type.t FullEnvi.t =
  let descriptor depth (path, base) =
    let x = { BoundName.path_name = PathName.of_name path base; depth } in
    Effect.Descriptor.singleton x [] in
  let d depth xs : Effect.Descriptor.t =
    Effect.Descriptor.union (List.map (descriptor depth) xs) in
  let typ_d (x : int) : Effect.Descriptor.t =
    let i = string_of_int x in
    Effect.Descriptor.singleton
      { BoundName.depth = 0; BoundName.path_name =
        (PathName.of_name ["Effect"; "State"] "state") }
      [Effect.PureType.Variable i] in
  let add_exn path base = add_exception_with_effects path base in
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
  |> Var.add [] "read_counter" (Arrow (d 0 [[], "Counter"], Pure))
  |> Descriptor.add [] "NonTermination"
  |> Var.add [] "not_terminated" (Arrow (d 0 [[], "NonTermination"], Pure))

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
  (* Comparisons *)
  |> Var.add [] "equiv_decb" Pure
  |> Var.add [] "nequiv_decb" Pure
  (* Boolean operations *)
  |> Var.add [] "negb" Pure
  |> Var.add [] "andb" Pure
  |> Var.add [] "orb" Pure
  (* Composition operators *)
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
  (* String operations *)
  |> Var.add ["String"] "append" Pure
  (* Pair operations *)
  |> Var.add [] "fst" Pure
  |> Var.add [] "snd" Pure

  |> enter_module (CoqName.Name "OCaml")
  (* Values specific to the translation to Coq *)
  |> Var.add [] "assert" (Arrow (d 0 [[], "Assert_failure"], Pure))
  (* Predefined exceptions *)
  |> Typ.add [] "exn" Pure
  |> add_exn [] "Match_failure"
  |> add_exn [] "Assert_failure"
  |> add_exn [] "Invalid_argument"
  |> add_exn [] "Failure"
  |> add_exn [] "Not_found"
  |> add_exn [] "Out_of_memory"
  |> add_exn [] "Stack_overflow"
  |> add_exn [] "Sys_error"
  |> add_exn [] "End_of_file"
  |> add_exn [] "Division_by_zero"
  |> add_exn [] "Sys_blocked_io"
  |> add_exn [] "Undefined_recursive_module"
  (* State *)
  |> Descriptor.add ["Effect"; "State"] "state"
  |> Typ.add ["Effect"; "State"] "t" (Arrow (d 0 [["Effect"; "State"], "state"], Pure))
  |> Var.add ["Effect"; "State"] "peekstate" Pure
  |> Var.add ["Effect"; "State"] "global" Pure
  |> Var.add ["Effect"; "State"] "read" (Arrow (typ_d 0, Pure))
  |> Var.add ["Effect"; "State"] "write" (Arrow (d 0 [], Arrow (typ_d 0, Pure)))

  (* Pervasives *)
  (* Exceptions *)
  |> Var.add ["Pervasives"] "invalid_arg" (Arrow (d 0 [[], "Invalid_argument"], Pure))
  |> Var.add ["Pervasives"] "failwith" (Arrow (d 0 [[], "Failure"], Pure))
  |> add_exn ["Pervasives"] "Exit"
  (* Comparisons *)
  |> Var.add ["Pervasives"] "lt" Pure
  |> Var.add ["Pervasives"] "gt" Pure
  |> Var.add ["Pervasives"] "le" Pure
  |> Var.add ["Pervasives"] "ge" Pure
  |> Var.add ["Pervasives"] "compare" Pure
  |> Var.add ["Pervasives"] "min" Pure
  |> Var.add ["Pervasives"] "max" Pure
  (* Composition operators *)
  |> Var.add ["Pervasives"] "reverse_apply" Pure
  (* Floating-point arithmetic *)
  (* Character operations *)
  |> Var.add ["Pervasives"] "int_of_char" Pure
  |> Var.add ["Pervasives"] "char_of_int" (Arrow (d 0 [[], "Invalid_argument"], Pure))
  (* Unit operations *)
  |> Var.add ["Pervasives"] "ignore" Pure
  (* String conversion functions *)
  |> Var.add ["Pervasives"] "string_of_bool" Pure
  |> Var.add ["Pervasives"] "bool_of_string" Pure
  |> Var.add ["Pervasives"] "string_of_int" Pure
  |> Var.add ["Pervasives"] "int_of_string" Pure
  (* List operations *)
  |> Var.add ["Pervasives"] "app" Pure
  (* Input/output *)
  (* Output functions on standard output *)
  |> Var.add ["Pervasives"] "print_char" (Arrow (d 1 [[], "IO"], Pure))
  |> Var.add ["Pervasives"] "print_string" (Arrow (d 1 [[], "IO"], Pure))
  |> Var.add ["Pervasives"] "print_int" (Arrow (d 1 [[], "IO"], Pure))
  |> Var.add ["Pervasives"] "print_endline" (Arrow (d 1 [[], "IO"], Pure))
  |> Var.add ["Pervasives"] "print_newline" (Arrow (d 1 [[], "IO"], Pure))
  (* Output functions on standard error *)
  |> Var.add ["Pervasives"] "prerr_char" (Arrow (d 1 [[], "IO"], Pure))
  |> Var.add ["Pervasives"] "prerr_string" (Arrow (d 1 [[], "IO"], Pure))
  |> Var.add ["Pervasives"] "prerr_int" (Arrow (d 1 [[], "IO"], Pure))
  |> Var.add ["Pervasives"] "prerr_endline" (Arrow (d 1 [[], "IO"], Pure))
  |> Var.add ["Pervasives"] "prerr_newline" (Arrow (d 1 [[], "IO"], Pure))
  (* Input functions on standard input *)
  |> Var.add ["Pervasives"] "read_line" (Arrow (d 1 [[], "IO"], Pure))
  |> Var.add ["Pervasives"] "read_int" (Arrow (d 1 [[], "IO"], Pure))
  (* General output functions *)
  (* General input functions *)
  (* Operations on large files *)
  (* References *)
  |> Var.add ["Pervasives"] "ref" Pure
  (* Operations on format strings *)
  (* Program termination *)
  |> leave_module Effect.Type.leave_prefix Effect.Type.resolve_open

  (* List *)
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
