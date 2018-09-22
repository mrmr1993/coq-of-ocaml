(** Local identifiers, used for variable names in patterns for example. *)
open SmartPrint
open Yojson.Basic

type t =
  | Name of Name.t
  | Alias of Name.t * Name.t (* (OCaml name, Coq name) *)

type t' = t
module Set = Set.Make (struct type t = t' let compare = compare end)
module Map = Map.Make (struct type t = t' let compare = compare end)

let of_names (name : Name.t) (coq_name : Name.t) : t =
  if name = coq_name then
    Name coq_name
  else
    Alias (name, coq_name)

let ocaml_name (x : t) : Name.t =
  match x with
  | Name name -> name
  | Alias (name, _) -> name

let assoc_names (x : t) : Name.t * Name.t =
  match x with
  | Name name -> (name, name)
  | Alias (name, coq_name) -> (name, coq_name)

let pp (x : t) : SmartPrint.t =
  match x with
  | Name name -> Name.pp name
  | Alias (name, coq_name) ->
    group @@ Name.pp name ^^ parens @@ !^ "=" ^^ Name.pp coq_name

(** Pretty-print a name to Coq. *)
let to_coq (x : t) : SmartPrint.t =
  match x with
  | Name name -> Name.to_coq name
  | Alias (_, coq_name) -> Name.to_coq coq_name

let to_json (x : t) : json =
  match x with
  | Name name -> `String name
  | Alias (name, coq_name) -> `List [`String name; `String coq_name]

let of_json (json : json) : t =
  match json with
  | `String x -> Name x
  | `List [`String name; `String coq_name] -> Alias (name, coq_name)
  | _ -> raise (Error.Json "String or string 2-tuple expected.")
