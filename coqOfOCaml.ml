open SmartPrint

(** Display on stdout the conversion in Coq of an OCaml structure. *)
let of_ocaml (structure : Typedtree.structure) (mode : string)
  (module_name : string) : unit =
  try
    let document =
      match mode with
      | "exp" ->
        let (_, defs) = Structure.of_structure PervasivesModule.env structure in
        let (_, defs) = Structure.monadise_let_rec PervasivesModule.env defs in
        Structure.pp Loc.pp defs
      | "effects" ->
        let (_, defs) = Structure.of_structure PervasivesModule.env structure in
        let (_, defs) = Structure.monadise_let_rec PervasivesModule.env defs in
        let (_, defs) =
          Structure.effects PervasivesModule.env_with_effects defs in
        let pp_annotation (l, effect) =
          OCaml.tuple [Loc.pp l; Effect.pp effect] in
        Structure.pp pp_annotation defs
      | "monadise" ->
        let (_, defs) = Structure.of_structure PervasivesModule.env structure in
        let (_, defs) = Structure.monadise_let_rec PervasivesModule.env defs in
        let (_, defs) =
          Structure.effects PervasivesModule.env_with_effects defs in
        let (_, defs) = Structure.monadise PervasivesModule.env defs in
        Structure.pp Loc.pp defs
      | "interface" ->
        let (_, defs) = Structure.of_structure PervasivesModule.env structure in
        let (_, defs) = Structure.monadise_let_rec PervasivesModule.env defs in
        let (_, defs) =
          Structure.effects PervasivesModule.env_with_effects defs in
        let interface = Interface.Interface
          (module_name, Interface.of_structures defs) in
        Interface.pp interface
      | "json" ->
        let (_, defs) = Structure.of_structure PervasivesModule.env structure in
        let (_, defs) = Structure.monadise_let_rec PervasivesModule.env defs in
        let (_, defs) =
          Structure.effects PervasivesModule.env_with_effects defs in
        let interface = Interface.Interface
          (module_name, Interface.of_structures defs) in
        !^ (Yojson.Safe.to_string ~std:true (`List [Interface.to_json interface]))
      | "v" ->
        let (_, defs) = Structure.of_structure PervasivesModule.env structure in
        let (_, defs) = Structure.monadise_let_rec PervasivesModule.env defs in
        let (_, defs) =
          Structure.effects PervasivesModule.env_with_effects defs in
        let (_, defs) = Structure.monadise PervasivesModule.env defs in
        concat (List.map (fun d -> d ^^ newline) [
          !^ "Require Import CoqOfOCaml." ^^ newline;
          !^ "Local Open Scope Z_scope.";
          !^ "Import ListNotations."]) ^^ newline ^^
        Structure.to_coq defs
      | _ -> failwith (Printf.sprintf "Unknown mode '%s'." mode) in
    to_stdout 80 2 document;
    print_newline ();
    flush stdout with
  | Envi.NotFound x ->
    failwith (to_string 80 2 @@ (PathName.pp x ^^ !^ "not found."))
  | Error.Make x ->
    failwith (to_string 80 2 @@ Error.pp x)

(** Parse a .cmt file to a typed AST. *)
let parse_cmt (file_name : string) : Typedtree.structure =
  let (_, cmt) = Cmt_format.read file_name in
  match cmt with
  | Some { Cmt_format.cmt_annots = Cmt_format.Implementation structure } ->
    structure
  | _ -> failwith "Cannot extract cmt data."

let module_name (file_name : string) : string =
  String.capitalize @@ Filename.chop_extension @@ Filename.basename file_name

(** The main function. *)
let main () =
  let file_name = ref None in
  let mode = ref "" in
  let options = [
    "-mode", Arg.Set_string mode, " exp, coq"] in
  let usage_msg = "Usage: ./coqOfOCaml.native file.cmt\nOptions are:" in
  Arg.parse options (fun arg -> file_name := Some arg) usage_msg;
  match !file_name with
  | None -> Arg.usage options usage_msg
  | Some file_name -> of_ocaml (parse_cmt file_name) !mode (module_name file_name);
  (*print_newline ();
  to_stdout 80 2 @@ Structure.pp [PervasivesModule.pervasives]*)

;;main ()