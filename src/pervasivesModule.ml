(** The initially opened module. *)
open FullEnvi
open Effect.Type
open SmartPrint

let env_with_effects (interfaces : (Name.t * string) list)
  : Effect.t FullEnvi.t =
  let bound_name full_path path base = {
      BoundName.full_path = PathName.of_name full_path base;
      local_path = PathName.of_name path base
    } in
  let descriptor (full_path, path, base) =
    let x = bound_name full_path path base in
    Effect.Descriptor.singleton x [] in
  let d xs : Effect.Descriptor.t =
    Effect.Descriptor.union (List.map descriptor xs) in
  let typ_d (x : int) : Effect.Descriptor.t =
    let i = string_of_int x in
    Effect.Descriptor.singleton
      (bound_name ["OCaml"; "Effect"; "State"] ["Effect"; "State"] "state")
      [Effect.PureType.Variable i] in
  let state_type (x : int) : Effect.PureType.t =
    let i = string_of_int x in
    Effect.PureType.Apply
      (bound_name ["OCaml"; "Effect"; "State"] ["Effect"; "State"] "state",
      [Effect.PureType.Variable i]) in
  let add_exn path base = add_exception_with_effects path base in
  let arrow x y = Effect.eff (Arrow (x, y)) in
  let pure = Effect.pure in
  FullEnvi.empty interfaces None
  (* Values specific to the translation to Coq *)
  |> Typ.add [] "nat" ()
  |> Constructor.add [] "O"
    (Effect.PureType.Apply (bound_name [] [] "nat", []), [])
  |> Constructor.add [] "S"
    (Effect.PureType.Apply (bound_name [] [] "nat", []),
    [Effect.PureType.Apply (bound_name [] [] "nat", [])])
  |> Typ.add [] "sum" ()
  |> Constructor.add [] "inl"
    (Effect.PureType.Apply (bound_name [] [] "sum",
      [Effect.PureType.Variable "A"; Effect.PureType.Variable "_"]),
    [Effect.PureType.Variable "A"])
  |> Constructor.add [] "inr"
    (Effect.PureType.Apply (bound_name [] [] "sum",
      [Effect.PureType.Variable "_"; Effect.PureType.Variable "A"]),
    [Effect.PureType.Variable "A"])
  |> Descriptor.add [] "IO" ()
  |> Descriptor.add [] "Counter" ()
  |> Var.add [] "read_counter" (arrow (d [[], [], "Counter"]) Pure)
  |> Descriptor.add [] "NonTermination" ()
  |> Var.add [] "not_terminated" (arrow (d [[], [], "NonTermination"]) Pure)
  |> Var.add ["OCaml"; "Basics"] "for_to" pure
  |> Var.add ["OCaml"; "Basics"] "for_downto" pure

  (* The core library *)
  (* Built-in types *)
  |> Typ.add [] "Z" ()
  |> Typ.add [] "ascii" ()
  |> Typ.add [] "string" ()
  |> Typ.add [] "bool" ()
  |> Constructor.add [] "false"
    (Effect.PureType.Apply (bound_name [] [] "bool", []), [])
  |> Constructor.add [] "true"
    (Effect.PureType.Apply (bound_name [] [] "bool", []), [])
  |> Typ.add [] "unit" ()
  |> Constructor.add [] "tt"
    (Effect.PureType.Apply (bound_name [] [] "unit", []), [])
  |> Typ.add [] "list" ()
  |> Constructor.add [] "[]"
    (Effect.PureType.Apply (bound_name [] [] "list", [Effect.PureType.Variable "_"]), [])
  |> Constructor.add [] "cons"
    (Effect.PureType.Apply (bound_name [] [] "list", [Effect.PureType.Variable "A"]),
    [Effect.PureType.Variable "A";
      Effect.PureType.Apply (bound_name [] [] "list", [Effect.PureType.Variable "A"])])
  |> Typ.add [] "option" ()
  |> Constructor.add [] "None"
    (Effect.PureType.Apply (bound_name [] [] "option", [Effect.PureType.Variable "_"]), [])
  |> Constructor.add [] "Some"
    (Effect.PureType.Apply (bound_name [] [] "option", [Effect.PureType.Variable "A"]),
    [Effect.PureType.Variable "A"])
  (* Comparisons *)
  |> Var.add [] "equiv_decb" pure
  |> Var.add [] "nequiv_decb" pure
  (* Boolean operations *)
  |> Var.add [] "negb" pure
  |> Var.add [] "andb" pure
  |> Var.add [] "orb" pure
  (* Composition operators *)
  |> Var.add [] "apply" pure
  (* Integer arithmetic *)
  |> Var.add ["Z"] "opp" pure
  |> Var.add [] "" pure
  |> Var.add ["Z"] "succ" pure
  |> Var.add ["Z"] "pred" pure
  |> Var.add ["Z"] "add" pure
  |> Var.add ["Z"] "sub" pure
  |> Var.add ["Z"] "mul" pure
  |> Var.add ["Z"] "div" pure
  |> Var.add ["Z"] "modulo" pure
  |> Var.add ["Z"] "abs" pure
  (* Bitwise operations *)
  |> Var.add ["Z"] "land" pure
  |> Var.add ["Z"] "lor" pure
  |> Var.add ["Z"] "lxor" pure
  |> Var.add ["Z"] "shiftl" pure
  |> Var.add ["Z"] "shiftr" pure
  (* String operations *)
  |> Var.add ["String"] "append" pure
  (* Pair operations *)
  |> Var.add [] "fst" pure
  |> Var.add [] "snd" pure

  |> enter_module (CoqName.Name "OCaml")
  (* Values specific to the translation to Coq *)
  |> Var.add [] "assert" (arrow (d [["OCaml"], [], "Assert_failure"]) Pure)
  (* Predefined exceptions *)
  |> Typ.add [] "exn" ()
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
  |> Descriptor.add ["Effect"; "State"] "state" ()
  |> Typ.add ["Effect"; "State"] "t" ()
  |> Var.add ["Effect"; "State"] "global" pure
  |> Function.add ["Effect"; "State"] "read"
    (arrow (typ_d 0) Pure,
    Effect.PureType.Arrow
      (state_type 0, Effect.PureType.Variable "0"))
  |> Function.add ["Effect"; "State"] "write"
    (arrow (d []) (Arrow (typ_d 0, Pure)),
    Effect.PureType.Arrow
      (state_type 0,
        Effect.PureType.Arrow
          (Effect.PureType.Variable "0",
          Effect.PureType.Apply (bound_name [] [] "unit", []))))

  (* Pervasives *)
  (* Exceptions *)
  |> Var.add ["Pervasives"] "invalid_arg" (arrow (d [["OCaml"], [], "Invalid_argument"]) Pure)
  |> Var.add ["Pervasives"] "failwith" (arrow (d [["OCaml"], [], "Failure"]) Pure)
  |> add_exn ["Pervasives"] "Exit"
  (* Comparisons *)
  |> Var.add ["Pervasives"] "lt" pure
  |> Var.add ["Pervasives"] "gt" pure
  |> Var.add ["Pervasives"] "le" pure
  |> Var.add ["Pervasives"] "ge" pure
  |> Var.add ["Pervasives"] "compare" pure
  |> Var.add ["Pervasives"] "min" pure
  |> Var.add ["Pervasives"] "max" pure
  (* Composition operators *)
  |> Var.add ["Pervasives"] "reverse_apply" pure
  (* Floating-point arithmetic *)
  (* Character operations *)
  |> Var.add ["Pervasives"] "int_of_char" pure
  |> Var.add ["Pervasives"] "char_of_int" (arrow (d [["OCaml"], [], "Invalid_argument"]) Pure)
  (* Unit operations *)
  |> Var.add ["Pervasives"] "ignore" pure
  (* String conversion functions *)
  |> Var.add ["Pervasives"] "string_of_bool" pure
  |> Var.add ["Pervasives"] "bool_of_string" pure
  |> Var.add ["Pervasives"] "string_of_int" pure
  |> Var.add ["Pervasives"] "int_of_string" pure
  (* List operations *)
  |> Var.add ["Pervasives"] "app" pure
  (* Input/output *)
  (* Output functions on standard output *)
  |> Var.add ["Pervasives"] "print_char" (arrow (d [[], [], "IO"]) Pure)
  |> Var.add ["Pervasives"] "print_string" (arrow (d [[], [], "IO"]) Pure)
  |> Var.add ["Pervasives"] "print_int" (arrow (d [[], [], "IO"]) Pure)
  |> Var.add ["Pervasives"] "print_endline" (arrow (d [[], [], "IO"]) Pure)
  |> Var.add ["Pervasives"] "print_newline" (arrow (d [[], [], "IO"]) Pure)
  (* Output functions on standard error *)
  |> Var.add ["Pervasives"] "prerr_char" (arrow (d [[], [], "IO"]) Pure)
  |> Var.add ["Pervasives"] "prerr_string" (arrow (d [[], [], "IO"]) Pure)
  |> Var.add ["Pervasives"] "prerr_int" (arrow (d [[], [], "IO"]) Pure)
  |> Var.add ["Pervasives"] "prerr_endline" (arrow (d [[], [], "IO"]) Pure)
  |> Var.add ["Pervasives"] "prerr_newline" (arrow (d [[], [], "IO"]) Pure)
  (* Input functions on standard input *)
  |> Var.add ["Pervasives"] "read_line" (arrow (d [[], [], "IO"]) Pure)
  |> Var.add ["Pervasives"] "read_int" (arrow (d [[], [], "IO"]) Pure)
  (* General output functions *)
  (* General input functions *)
  (* Operations on large files *)
  (* References *)
  |> Function.add ["Pervasives"] "ref"
    (arrow (typ_d 0) Pure,
    Effect.PureType.Arrow (Effect.PureType.Variable "0", state_type 0))
  (* Operations on format strings *)
  (* Program termination *)
  |> leave_module localize_effects

  (* List *)
  |> fun env ->
       let lazy_loader = ref env in
       let run_in_external f env =
         let (x, env) = FullEnvi.run_in_env f env !lazy_loader in
         lazy_loader := env;
         x in
       lazy_loader := { !lazy_loader with
           run_in_external;
           convert = (fun x -> x);
           load_module = Interface.load_module
         };
       { env with run_in_external; convert = (fun x -> x) }
  |> enter_section
  |> open_module' Loc.Unknown ["OCaml"]
