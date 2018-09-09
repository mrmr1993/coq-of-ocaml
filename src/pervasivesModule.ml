(** The initially opened module. *)
open FullEnvi
open Effect.Type
open SmartPrint

let env_with_effects : Effect.Type.t FullEnvi.t =
  let bound_name depth full_path path base = {
      BoundName.full_path = PathName.of_name full_path base;
      local_path = PathName.of_name path base;
      depth
    } in
  let descriptor depth (full_path, path, base) =
    let x = bound_name depth full_path path base in
    Effect.Descriptor.singleton x [] in
  let d depth xs : Effect.Descriptor.t =
    Effect.Descriptor.union (List.map (descriptor depth) xs) in
  let typ_d (x : int) : Effect.Descriptor.t =
    let i = string_of_int x in
    Effect.Descriptor.singleton
      (bound_name 0 ["OCaml"; "Effect"; "State"] ["Effect"; "State"] "state")
      [Effect.PureType.Variable i] in
  let state_type (x : int) : Effect.PureType.t =
    let i = string_of_int x in
    Effect.PureType.Apply
      (bound_name 0 ["OCaml"; "Effect"; "State"] ["Effect"; "State"] "state",
      [Effect.PureType.Variable i]) in
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
  |> Var.add [] "read_counter" (Arrow (d 0 [[], [], "Counter"], Pure))
  |> Descriptor.add [] "NonTermination"
  |> Var.add [] "not_terminated" (Arrow (d 0 [[], [], "NonTermination"], Pure))

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
  |> Var.add [] "assert" (Arrow (d 0 [["OCaml"], [], "Assert_failure"], Pure))
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
  |> Typ.add ["Effect"; "State"] "t" (Arrow (d 0 [["OCaml"; "Effect"; "State"], ["Effect"; "State"], "state"], Pure))
  |> Var.add ["Effect"; "State"] "peekstate" Pure
  |> Var.add ["Effect"; "State"] "global" Pure
  |> Function.add ["Effect"; "State"] "read"
    (Arrow (typ_d 0, Pure))
    (Effect.PureType.Arrow
      (state_type 0, Effect.PureType.Variable "0"))
  |> Function.add ["Effect"; "State"] "write"
    (Arrow (d 0 [], Arrow (typ_d 0, Pure)))
    (Effect.PureType.Arrow
      (state_type 0,
        Effect.PureType.Arrow
          (Effect.PureType.Variable "0",
          Effect.PureType.Apply (bound_name 1 [] [] "unit", []))))

  (* Pervasives *)
  (* Exceptions *)
  |> Var.add ["Pervasives"] "invalid_arg" (Arrow (d 0 [["OCaml"], [], "Invalid_argument"], Pure))
  |> Var.add ["Pervasives"] "failwith" (Arrow (d 0 [["OCaml"], [], "Failure"], Pure))
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
  |> Var.add ["Pervasives"] "char_of_int" (Arrow (d 0 [["OCaml"], [], "Invalid_argument"], Pure))
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
  |> Var.add ["Pervasives"] "print_char" (Arrow (d 1 [[], [], "IO"], Pure))
  |> Var.add ["Pervasives"] "print_string" (Arrow (d 1 [[], [], "IO"], Pure))
  |> Var.add ["Pervasives"] "print_int" (Arrow (d 1 [[], [], "IO"], Pure))
  |> Var.add ["Pervasives"] "print_endline" (Arrow (d 1 [[], [], "IO"], Pure))
  |> Var.add ["Pervasives"] "print_newline" (Arrow (d 1 [[], [], "IO"], Pure))
  (* Output functions on standard error *)
  |> Var.add ["Pervasives"] "prerr_char" (Arrow (d 1 [[], [], "IO"], Pure))
  |> Var.add ["Pervasives"] "prerr_string" (Arrow (d 1 [[], [], "IO"], Pure))
  |> Var.add ["Pervasives"] "prerr_int" (Arrow (d 1 [[], [], "IO"], Pure))
  |> Var.add ["Pervasives"] "prerr_endline" (Arrow (d 1 [[], [], "IO"], Pure))
  |> Var.add ["Pervasives"] "prerr_newline" (Arrow (d 1 [[], [], "IO"], Pure))
  (* Input functions on standard input *)
  |> Var.add ["Pervasives"] "read_line" (Arrow (d 1 [[], [], "IO"], Pure))
  |> Var.add ["Pervasives"] "read_int" (Arrow (d 1 [[], [], "IO"], Pure))
  (* General output functions *)
  (* General input functions *)
  (* Operations on large files *)
  (* References *)
  |> Function.add ["Pervasives"] "ref"
    (Arrow (typ_d 0, Pure))
    (Effect.PureType.Arrow (Effect.PureType.Variable "0", state_type 0))
  (* Operations on format strings *)
  (* Program termination *)
  |> fun env -> leave_module
      (FullMod.localize_type (FullEnvi.Descriptor.has_name env)) env

  (* List *)
  |> fun env ->
       let lazy_loader = ref env in
       let default_bound = env.bound_external in
       let bound_in_flight = ref PathName.Set.empty in
       let bound_external required_modules find has_name x =
         if PathName.Set.mem x !bound_in_flight then
           default_bound required_modules find has_name x
         else begin
           bound_in_flight := PathName.Set.add x !bound_in_flight;
           lazy_loader := FullEnvi.combine !lazy_loader
             (LazyLoader.load_module x !lazy_loader);
           required_modules := !((!lazy_loader).required_modules);
           let bound = FullEnvi.bound_name_opt find has_name x !lazy_loader in
           bound_in_flight := PathName.Set.remove x !bound_in_flight;
           bound
         end in
       let default_find = env.find_external in
       let find_in_flight = ref PathName.Set.empty in
       let find_external loc x =
         if PathName.Set.mem x.BoundName.full_path !find_in_flight then
           default_find loc x
         else begin
           find_in_flight := PathName.Set.add x.BoundName.full_path
             !find_in_flight;
           let value = FullEnvi.find loc x !lazy_loader in
           find_in_flight := PathName.Set.remove x.BoundName.full_path
             !find_in_flight;
           value
         end in
       let default_find_module = env.find_external_module in
       let find_module_in_flight = ref PathName.Set.empty in
       let find_external_module loc x =
         if PathName.Set.mem x.BoundName.full_path !find_module_in_flight then
           default_find_module loc x
         else begin
           find_module_in_flight := PathName.Set.add x.BoundName.full_path
             !find_module_in_flight;
           let m = FullEnvi.Module.find loc x !lazy_loader in
           find_module_in_flight := PathName.Set.remove x.BoundName.full_path
             !find_module_in_flight;
           m
         end in
       lazy_loader := { !lazy_loader with bound_external; find_external;
         find_external_module };
       { env with bound_external; find_external; find_external_module }
  |> enter_section
  |> open_module' Loc.Unknown ["OCaml"]

let show out_channel : unit =
  to_out_channel 80 2 out_channel (FullEnvi.pp env_with_effects)

(* show stdout;; *)

let env : unit FullEnvi.t = FullEnvi.map (fun _ -> ()) env_with_effects
