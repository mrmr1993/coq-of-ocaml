(** The initially opened module. *)
open FullEnvi
open SmartPrint

let env_with_effects (interfaces : (Name.t * string) list)
  : Type.t FullEnvi.t =
  let bound_name full_path path base = {
      BoundName.full_path = PathName.of_name full_path base;
      local_path = PathName.of_name path base
    } in
  let descriptor (full_path, path, base) =
    let x = bound_name full_path path base in
    Effect.Descriptor.singleton x [] in
  let d xs : Effect.Descriptor.t =
    Effect.Descriptor.union (List.map descriptor xs) in
  let typ_d (x : string) : Effect.Descriptor.t =
    Effect.Descriptor.singleton
      (bound_name ["OCaml"; "Effect"; "State"] ["Effect"; "State"] "state")
      [Type.Variable x] in
  let state_type (x : string) : Type.t =
    Type.Apply
      (bound_name ["OCaml"; "Effect"; "State"] ["Effect"; "State"] "state",
      [Type.Variable x]) in
  let add_exn path base = add_exception_with_effects path base in
  let arrow xs = List.fold_right (fun x typ ->
    Effect.Type.arrow (d x) typ) xs Effect.pure in
  let pure = Effect.pure in
  FullEnvi.empty interfaces None
  (* Values specific to the translation to Coq *)
  |> TypeDefinition.update_env
    (TypeDefinition.Inductive (CoqName.Name "nat", [], [
      (CoqName.Name "O", []);
      (CoqName.Name "S", [Type.Apply (bound_name [] [] "nat", [])])
    ]))
  |> TypeDefinition.update_env
    (TypeDefinition.Inductive (CoqName.Name "sum", ["A"; "B"], [
      (CoqName.Name "inl", [Type.Variable "A"]);
      (CoqName.Name "inr", [Type.Variable "B"])
    ]))
  |> Descriptor.add [] "IO" ()
  |> Descriptor.add [] "Counter" ()
  |> Var.add [] "read_counter" (arrow [[[], [], "Counter"]])
  |> Descriptor.add [] "NonTermination" ()
  |> Var.add [] "not_terminated" (arrow [[[], [], "NonTermination"]])
  |> Var.add ["OCaml"; "Basics"] "for_to" pure
  |> Var.add ["OCaml"; "Basics"] "for_downto" pure

  (* The core library *)
  (* Built-in types *)
  |> Typ.add [] "Z" (TypeDefinition.Abstract (CoqName.Name "Z", []))
  |> Typ.add [] "ascii" (TypeDefinition.Abstract (CoqName.Name "ascii", []))
  |> Typ.add [] "string" (TypeDefinition.Abstract (CoqName.Name "string", []))
  |> TypeDefinition.update_env
    (TypeDefinition.Inductive (CoqName.Name "bool", [], [
      (CoqName.Name "false", []);
      (CoqName.Name "true", [])
    ]))
  |> TypeDefinition.update_env
    (TypeDefinition.Inductive (CoqName.Name "unit", [], [
      (CoqName.Name "tt", [])
    ]))
  |> TypeDefinition.update_env
    (TypeDefinition.Inductive (CoqName.Name "list", ["A"], [
      (CoqName.Name "[]", []);
      (CoqName.Name "cons",
        [Type.Variable "A";
        Type.Apply (bound_name [] [] "list", [Type.Variable "A"])])
    ]))
  |> TypeDefinition.update_env
    (TypeDefinition.Inductive (CoqName.Name "option", ["A"], [
      (CoqName.Name "None", []);
      (CoqName.Name "Some", [Type.Variable "A"])
    ]))
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
  |> Var.add [] "assert" (arrow [[["OCaml"], [], "Assert_failure"]])
  (* Predefined exceptions *)
  |> Typ.add [] "exn" (TypeDefinition.Abstract (CoqName.Name "exn", []))
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
  |> Typ.add ["Effect"; "State"] "t" (TypeDefinition.Abstract (CoqName.Name "t", []))
  |> Var.add ["Effect"; "State"] "global" pure
  |> Var.add ["Effect"; "State"] "read"
    (Type.Arrow (state_type "0", Type.Monad (typ_d "0", Type.Variable "0")))
  |> Var.add ["Effect"; "State"] "write"
    (Type.Arrow (state_type "0", Type.Arrow (Type.Variable "0",
      Type.Monad (typ_d "0", Type.Apply (bound_name [] [] "unit", [])))))

  (* Pervasives *)
  (* Exceptions *)
  |> Var.add ["Pervasives"] "invalid_arg" (arrow [[["OCaml"], [], "Invalid_argument"]])
  |> Var.add ["Pervasives"] "failwith" (arrow [[["OCaml"], [], "Failure"]])
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
  |> Var.add ["Pervasives"] "char_of_int" (arrow [[["OCaml"], [], "Invalid_argument"]])
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
  |> Var.add ["Pervasives"] "print_char" (arrow [[[], [], "IO"]])
  |> Var.add ["Pervasives"] "print_string" (arrow [[[], [], "IO"]])
  |> Var.add ["Pervasives"] "print_int" (arrow [[[], [], "IO"]])
  |> Var.add ["Pervasives"] "print_endline" (arrow [[[], [], "IO"]])
  |> Var.add ["Pervasives"] "print_newline" (arrow [[[], [], "IO"]])
  (* Output functions on standard error *)
  |> Var.add ["Pervasives"] "prerr_char" (arrow [[[], [], "IO"]])
  |> Var.add ["Pervasives"] "prerr_string" (arrow [[[], [], "IO"]])
  |> Var.add ["Pervasives"] "prerr_int" (arrow [[[], [], "IO"]])
  |> Var.add ["Pervasives"] "prerr_endline" (arrow [[[], [], "IO"]])
  |> Var.add ["Pervasives"] "prerr_newline" (arrow [[[], [], "IO"]])
  (* Input functions on standard input *)
  |> Var.add ["Pervasives"] "read_line" (arrow [[[], [], "IO"]])
  |> Var.add ["Pervasives"] "read_int" (arrow [[[], [], "IO"]])
  (* General output functions *)
  (* General input functions *)
  (* Operations on large files *)
  (* References *)
  |> Var.add ["Pervasives"] "ref"
    (Type.Arrow (Type.Variable "0", Monad (typ_d "0", state_type "0")))
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
