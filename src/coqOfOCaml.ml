open SmartPrint

let exp (structure : Typedtree.structure) : Loc.t Structure.t list =
  let (_, defs) = Structure.of_structure PervasivesModule.env structure in
  snd @@ Structure.monadise_let_rec PervasivesModule.env defs

let effects (exp : Loc.t Structure.t list)
  : (Loc.t * Effect.t) Structure.t list =
  snd @@ Structure.effects PervasivesModule.env_with_effects @@ exp

let monadise (effects : (Loc.t * Effect.t) Structure.t list)
  : Loc.t Structure.t list =
  snd @@ Structure.monadise PervasivesModule.env @@ effects

let interface (module_name : string)
  (effects : (Loc.t * Effect.t) Structure.t list) : Interface.t =
  Interface.Interface (module_name, Interface.of_structures effects)

let coq (monadise : Loc.t Structure.t list) : SmartPrint.t =
  concat (List.map (fun d -> d ^^ newline) [
    !^ "Require Import OCaml.OCaml." ^^ newline;
    !^ "Local Open Scope Z_scope.";
    !^ "Local Open Scope type_scope.";
    !^ "Import ListNotations."]) ^^ newline ^^
    Structure.to_coq monadise

let map_apply (x : 'a) (l : ('a -> unit) list) : unit =
  List.iter (fun f -> f x) l

let result_map (f : 'a -> 'b) (gl : ('b -> unit) list) : ('a -> unit) list =
  match gl with
  | [] -> []
  | _ -> [fun a -> map_apply (f a) gl]

let to_out_channel (c : out_channel) (d : SmartPrint.t) =
  SmartPrint.to_out_channel 80 2 c d;
  output_char c '\n';
  flush c

let output_exp (c : out_channel) (exp : Loc.t Structure.t list) : unit =
  to_out_channel c @@ Structure.pps Loc.pp exp

let output_effects (c : out_channel)
  (effects : (Loc.t * Effect.t) Structure.t list) : unit =
  let pp_annotation (l, effect) =
    OCaml.tuple [Loc.pp l; Effect.pp effect] in
  to_out_channel c @@ Structure.pps pp_annotation effects

let output_interface (c : out_channel) (interface : Interface.t) : unit =
  to_out_channel c @@ !^ (Interface.to_json_string interface)

let output_monadise (c : out_channel) (monadise : Loc.t Structure.t list)
  : unit =
  to_out_channel c @@ Structure.pps Loc.pp monadise

(** Display on stdout the conversion in Coq of an OCaml structure. *)
let of_ocaml (structure : Typedtree.structure) (mode : string)
  (module_name : string) : unit =
  try
    let (exp_l, effects_l, interface_l, monadise_l, coq_l) =
      if String.equal "exp" mode then
        [output_exp stdout], [], [], [], []
      else if String.equal "effects" mode then
        [], [output_effects stdout], [], [], []
      else if String.equal "interface" mode then
        [], [], [output_interface stdout], [], []
      else if String.equal "monadise" mode then
        [], [], [], [output_monadise stdout], []
      else if String.equal "v" mode then
        [], [], [], [], [to_out_channel stdout]
      else
        [], [], [], [], [] in

    map_apply structure
      (result_map exp (exp_l @
      (result_map effects (effects_l @
      (result_map (interface module_name) interface_l) @
      (result_map monadise (monadise_l @
      (result_map coq coq_l)))))))
 with
  | Error.Make x ->
    prerr_endline @@ to_string 80 2 @@ (!^ "Error:" ^^ Error.pp x);
    exit 2

(** Parse a .cmt file to a typed AST. *)
let parse_cmt (file_name : string) : Typedtree.structure =
  let (_, cmt) = Cmt_format.read file_name in
  match cmt with
  | Some { Cmt_format.cmt_annots = Cmt_format.Implementation structure } ->
    structure
  | _ -> failwith "Cannot extract cmt data."

let module_name (file_name : string) : string =
  String.capitalize_ascii @@ Filename.chop_extension @@ Filename.basename file_name

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

(** The main function. *)
let main () =
  let file_name = ref None in
  let mode = ref "" in
  let dir = ref "" in
  let options = [
    "-mode", Arg.Set_string mode,
      " v (generate Coq .v files, you probably want this option), exp (the simplified expression tree), effects (the inferred effects), monadise (the expression tree after monadisation), interface (the equivalent of .mli with effects)";
    "-I", Arg.Tuple [Arg.Set_string dir; Arg.String (fun coq_name ->
        LazyLoader.interfaces := (Name.of_string coq_name, !dir) :: !LazyLoader.interfaces)],
      "dir coqdir\t\tsearch physical dir for interface files, mapped to logical coqdir"] in
  let usage_msg = "Usage: ./coqOfOCaml.native file.cmt\nOptions are:" in

  (* Add the default interfaces directory to the interfaces list. *)
  (match find_interfaces_dir Sys.executable_name with
  | Some interfaces_dir ->
    LazyLoader.interfaces := ("OCaml", interfaces_dir) :: !LazyLoader.interfaces
  | None ->
    prerr_endline @@ to_string 80 2 (!^ "Warning: interfaces directory was not found"));

  Arg.parse options (fun arg -> file_name := Some arg) usage_msg;
  match !file_name with
  | None -> Arg.usage options usage_msg
  | Some file_name -> of_ocaml (parse_cmt file_name) !mode (module_name file_name);

;;main ()
