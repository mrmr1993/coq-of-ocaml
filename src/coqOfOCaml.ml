open SmartPrint

let exp  (env : unit FullEnvi.t) (structure : Typedtree.structure)
  : (Loc.t * Type.t) Structure.t list =
  let (_, defs) = Structure.of_structure env structure in
  snd @@ Structure.monadise_let_rec env defs

let effects (env : Effect.t FullEnvi.t)
  (exp : (Loc.t * Type.t) Structure.t list)
  : (Loc.t * Effect.t) Structure.t list =
  snd @@ Structure.effects env @@ exp

let monadise (env : unit FullEnvi.t)
  (effects : (Loc.t * Effect.t) Structure.t list) : Loc.t Structure.t list =
  snd @@ Structure.monadise env @@ effects

let interface (module_name : string)
  (effects : (Loc.t * Effect.t) Structure.t list) : Interface.t =
  Interface.Interface (CoqName.Name module_name, Interface.of_structures effects)

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

let output_exp (c : out_channel) (exp : (Loc.t * Type.t) Structure.t list)
  : unit =
  let pp_annotation (l, typ) = Loc.pp l in
  to_out_channel c @@ Structure.pps pp_annotation exp

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

type mode_files = {
  v : string list;
  interface : string list;
  exp : string list;
  effects : string list;
  monadise : string list
}

let empty_mode_files : mode_files = {
  v = [];
  interface = [];
  exp = [];
  effects = [];
  monadise = []
}

let mode_files_localise (dir : string) (mode_files : mode_files) : mode_files =
  let localise file =
    if Filename.is_implicit file then Filename.concat dir file else file in
  { v = List.map localise mode_files.v;
    interface = List.map localise mode_files.interface;
    exp = List.map localise mode_files.exp;
    effects = List.map localise mode_files.effects;
    monadise = List.map localise mode_files.monadise }

let stropt_eq (str : string) (opt_str : string option) : bool =
  match opt_str with
  | Some str2 -> String.equal str str2
  | None -> false

let do_out (f : out_channel -> 'a -> 'b) (file_name : string) (x : 'a) : 'b =
  let out = open_out file_name in
  let ret = f out x in
  close_out out;
  ret

(** Display on stdout the conversion in Coq of an OCaml structure. *)
let of_ocaml (interfaces : (Name.t * string) list)
  (structure : Typedtree.structure) (mode : string option)
  (mode_files : mode_files) (module_name : string) : unit =
  try
    let env_with_effects = PervasivesModule.env_with_effects interfaces in
    let env = FullEnvi.map (fun _ -> ()) env_with_effects in
    let (exp_l, effects_l, interface_l, monadise_l, coq_l) =
      if stropt_eq "exp" mode then
        [output_exp stdout], [], [], [], []
      else if stropt_eq "effects" mode then
        [], [output_effects stdout], [], [], []
      else if stropt_eq "interface" mode then
        [], [], [output_interface stdout], [], []
      else if stropt_eq "monadise" mode then
        [], [], [], [output_monadise stdout], []
      else if stropt_eq "v" mode then
        [], [], [], [], [to_out_channel stdout]
      else
        [], [], [], [], [] in

    let exp_l = exp_l @
      (List.map (do_out output_exp) mode_files.exp) in
    let effects_l = effects_l @
      (List.map (do_out output_effects) mode_files.effects) in
    let interface_l = interface_l @
      (List.map (do_out output_interface) mode_files.interface) in
    let monadise_l = monadise_l @
      (List.map (do_out output_monadise) mode_files.monadise) in
    let coq_l = coq_l @
      (List.map (do_out to_out_channel) mode_files.v) in

    map_apply structure
      (result_map (exp env) (exp_l @
      (result_map (effects env_with_effects) (effects_l @
      (result_map (interface module_name) interface_l) @
      (result_map (monadise env) (monadise_l @
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

let bare_file_name (file_name : string) : string =
  Filename.chop_extension @@ Filename.basename file_name

let module_name (file_name : string) : string =
  String.capitalize_ascii file_name

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
  let mode = ref None in
  let mode_files = ref empty_mode_files in
  let dir = ref "" in
  let output_dir = ref "" in
  let stdlib = ref true in
  let output_all = ref false in
  let output_default_force = ref false in
  let interfaces = ref [] in
  let options = Arg.align [
    "--v", Arg.String
        (fun file -> mode_files := {!mode_files with v = file :: !mode_files.v}),
      "filename\toutput the generated Coq .v file to filename";
    "--interface", Arg.String
        (fun file -> mode_files := {!mode_files with interface = file :: !mode_files.interface}),
      "filename\toutput the generated interface file (similar to an .mli with effects) to filename";
    "--exp", Arg.String
        (fun file -> mode_files := {!mode_files with exp = file :: !mode_files.exp}),
      "filename\toutput the simplified expression tree to filename";
    "--effects", Arg.String
        (fun file -> mode_files := {!mode_files with effects = file :: !mode_files.effects}),
      "filename\toutput the inferred effects to filename";
    "--monadise", Arg.String
        (fun file -> mode_files := {!mode_files with monadise = file :: !mode_files.monadise}),
      "filename\toutput the expression tree after monadisation to filename";
    "--all", Arg.Set output_all,
      "  \toutput all modes to their default filenames in the output directory";
    "--default", Arg.Set output_default_force,
      "\toutput v and interface modes to their default filenames in the output directory";
    "--mode", Arg.Symbol
        (["v"; "interface"; "exp"; "effects"; "monadise"], fun m -> mode := Some m),
      "\tdirect the mode's output to stdout";
    "-I", Arg.Tuple [Arg.Set_string dir; Arg.String (fun coq_name ->
        interfaces := (Name.of_string coq_name, !dir) :: !interfaces)],
      "dir coqdir\tsearch physical dir for interface files, mapped to logical coqdir";
    "-o", Arg.Set_string output_dir,
      "dir\tset the output directory to dir";
    "--no-stdlib", Arg.Clear stdlib,
      "\tdon't include the interfaces directory containing the standard interfaces"] in
  let usage_msg = "Usage: ./coqOfOCaml.native file.cmt\nOptions are:" in

  if !stdlib then begin
    (* Add the default interfaces directory to the interfaces list. *)
    (match find_interfaces_dir Sys.executable_name with
    | Some interfaces_dir ->
      interfaces := ("OCaml", interfaces_dir) :: !interfaces
    | None ->
      prerr_endline @@ to_string 80 2 (!^ "Warning: interfaces directory was not found"));
  end else ();

  Arg.parse options (fun arg -> file_name := Some arg) usage_msg;
  match !file_name with
  | None -> Arg.usage options usage_msg
  | Some file_name ->
    let bare_file_name = bare_file_name file_name in
    if !output_all then
      mode_files := {
        v = !mode_files.v @ [module_name bare_file_name ^ ".v"];
        interface = !mode_files.interface @ [bare_file_name ^ ".interface"];
        exp = !mode_files.exp @ [bare_file_name ^ ".exp"];
        effects = !mode_files.effects @ [bare_file_name ^ ".effects"];
        monadise = !mode_files.monadise @ [bare_file_name ^ ".monadise"]
      }
    else if !output_default_force ||
           (!mode_files == empty_mode_files && !mode == None) then
      mode_files := {!mode_files with
        v = !mode_files.v @ [module_name bare_file_name ^ ".v"];
        interface = !mode_files.interface @ [bare_file_name ^ ".interface"]
      };
    if !output_dir != "" then
      mode_files := mode_files_localise !output_dir !mode_files;
    of_ocaml !interfaces (parse_cmt file_name) !mode !mode_files
      (module_name bare_file_name);

;;main ()
