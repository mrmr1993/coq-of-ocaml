open SmartPrint

module Segment = struct
  type 'a t = {
    opens : Name.t list list;
    names : 'a PathName.Map.t }

  let pp (segment : 'a t) : SmartPrint.t =
    nest (
      nest (!^ "open" ^^ OCaml.list (fun path ->
        double_quotes (separate (!^ ".") (List.map Name.pp path)))
        segment.opens) ^^
      OCaml.list (fun (x, _) -> PathName.pp x)
        (PathName.Map.bindings segment.names))

  let cardinal (segment : 'a t) : int =
    PathName.Map.cardinal segment.names

  let empty : 'a t = {
    opens = [[]]; (** By default we open the empty path. *)
    names = PathName.Map.empty }

  let add (x : PathName.t) (v : 'a) (segment : 'a t) : 'a t =
    { segment with names = PathName.Map.add x v segment.names }

  let mem (x : PathName.t) (segment : 'a t) : bool =
    PathName.Map.mem x segment.names

  let find (x : PathName.t) (segment : 'a t) : 'a =
    PathName.Map.find x segment.names

  let map (f : 'a -> 'b) (segment : 'a t) : 'b t =
    { segment with names = PathName.Map.map f segment.names }

  let merge (segment1 : 'a t) (segment2 : 'a t) (prefix : Name.t -> 'a -> 'a)
    (module_name : Name.t) : 'a t =
    PathName.Map.fold (fun x v segment2 ->
      let x = { x with PathName.path = module_name :: x.PathName.path } in
      add x (prefix module_name v) segment2)
      segment1.names segment2

  let open_module (segment : 'a t) (module_name : Name.t list) : 'a t =
    { segment with opens = module_name :: segment.opens }
end

module Mod = struct
  type 'a t = {
    opens : Name.t list list;
    vars : 'a PathName.Map.t;
    typs : unit PathName.Map.t;
    descriptors: unit PathName.Map.t;
    constructors : unit PathName.Map.t;
    fields : unit PathName.Map.t }

  let empty : 'a t = {
    opens = [[]]; (** By default we open the empty path. *)
    vars = PathName.Map.empty;
    typs = PathName.Map.empty;
    descriptors = PathName.Map.empty;
    constructors = PathName.Map.empty;
    fields = PathName.Map.empty }

  let pp (m : 'a t) : SmartPrint.t =
    let pp_map map = OCaml.list (fun (x, _) -> PathName.pp x)
      (PathName.Map.bindings map) in
    group (
      nest (!^ "open" ^^ OCaml.list (fun path ->
        double_quotes (separate (!^ ".") (List.map Name.pp path)))
        m.opens) ^^ newline ^^
      !^ "vars:" ^^ nest (pp_map m.vars) ^^ newline ^^
      !^ "typs:" ^^ nest (pp_map m.typs) ^^ newline ^^
      !^ "descriptors:" ^^ nest (pp_map m.descriptors) ^^ newline ^^
      !^ "constructors:" ^^ nest (pp_map m.constructors) ^^ newline ^^
      !^ "fields:" ^^ nest (pp_map m.fields))

  let open_module (m : 'a t) (module_name : Name.t list) : 'a t =
    { m with opens = module_name :: m.opens }

  let map_union (f : PathName.t -> PathName.t) (g : PathName.t -> 'a -> 'a)
    (m1 : 'a PathName.Map.t) (m2 : 'a PathName.Map.t) : 'a PathName.Map.t =
    PathName.Map.fold (fun name value newmap ->
      PathName.Map.add (f name) (g name value) newmap
    ) m1 m2

  let close_module (module_name : Name.t) (prefix : Name.t -> 'a -> 'a)
    (m1 : 'a t) (m2 : 'a t) : 'a t =
    let add_to_path x =
      { x with PathName.path = module_name :: x.PathName.path } in
    let unit_map_union m1 m2 = map_union add_to_path (fun _ () -> ()) m1 m2 in
  { opens = m2.opens;
    vars = map_union add_to_path (fun _ v -> prefix module_name v)
      m1.vars m2.vars;
    typs = unit_map_union m1.typs m2.typs;
    descriptors = unit_map_union m1.descriptors m2.descriptors;
    constructors = unit_map_union m1.constructors m2.constructors;
    fields = unit_map_union m1.fields m2.fields}

  let find_free_name (base_name : string) (env : 'a PathName.Map.t) : Name.t =
    let prefix_n s n =
      if n = 0 then
        Name.of_string s
      else
        Name.of_string @@ Printf.sprintf "%s_%d" s n in
    let rec first_n (n : int) : int =
      if PathName.Map.mem (PathName.of_name [] @@ prefix_n base_name n) env then
        first_n (n + 1)
      else
        n in
    prefix_n base_name (first_n 0)

  module Vars = struct
    let add (x : PathName.t) (v : 'a) (m : 'a t) : 'a t =
      { m with vars = PathName.Map.add x v m.vars }

    let mem (x : PathName.t) (m : 'a t) : bool =
      PathName.Map.mem x m.vars

    let find (x : PathName.t) (m : 'a t) : 'a =
      PathName.Map.find x m.vars

    let map (f : 'a -> 'b) (m : 'a t) : 'b t =
      { m with vars = PathName.Map.map f m.vars }

    (** Add a fresh local name beginning with [prefix] in [env]. *)
    let fresh (prefix : string) (v : 'a) (env : 'a t) : Name.t * 'a t =
      let name = find_free_name prefix env.vars in
      (name, add (PathName.of_name [] name) v env)
  end
  module Typs = struct
    let add (x : PathName.t) (m : 'a t) : 'a t =
      { m with typs = PathName.Map.add x () m.typs }

    let mem (x : PathName.t) (m : 'a t) : bool =
      PathName.Map.mem x m.typs

    let map (f : unit -> 'b) (m : 'a t) : 'b t =
      { m with typs = PathName.Map.map f m.typs }
  end
  module Descriptors = struct
    let add (x : PathName.t) (m : 'a t) : 'a t =
      { m with descriptors = PathName.Map.add x () m.descriptors }

    let mem (x : PathName.t) (m : 'a t) : bool =
      PathName.Map.mem x m.descriptors

    let map (f : unit -> 'b) (m : 'a t) : 'b t =
      { m with descriptors = PathName.Map.map f m.descriptors }
  end
  module Constructors = struct
    let add (x : PathName.t) (m : 'a t) : 'a t =
      { m with constructors = PathName.Map.add x () m.constructors }

    let mem (x : PathName.t) (m : 'a t) : bool =
      PathName.Map.mem x m.constructors

    let map (f : unit -> 'b) (m : 'a t) : 'b t =
      { m with constructors = PathName.Map.map f m.constructors }
  end
  module Fields = struct
    let add (x : PathName.t) (m : 'a t) : 'a t =
      { m with fields = PathName.Map.add x () m.fields }

    let mem (x : PathName.t) (m : 'a t) : bool =
      PathName.Map.mem x m.fields

    let map (f : unit -> 'b) (m : 'a t) : 'b t =
      { m with fields = PathName.Map.map f m.fields }
  end
end

type 'a t = 'a Segment.t list

let pp (env : 'a t) : SmartPrint.t =
  OCaml.list Segment.pp env

let rec size (env : 'a t) : int =
  match env with
  | [] -> 0
  | segment :: env -> Segment.cardinal segment + size env

let empty : 'a t = [Segment.empty]

let add (x : PathName.t) (v : 'a) (env : 'a t)
  : 'a t =
  match env with
  | segment :: env -> Segment.add x v segment :: env
  | [] -> failwith "The environment must be a non-empty list."

let rec find_first (f : 'a -> 'b option) (l : 'a list) : 'b option =
  match l with
  | [] -> None
  | x :: l ->
    (match f x with
    | None -> find_first f l
    | y -> y)

let rec depth (x : PathName.t) (env : 'a t) : (PathName.t * int) option =
  match env with
  | segment :: env ->
    if Segment.mem x segment then
      Some (x, 0)
    else
      segment.Segment.opens |> find_first (fun path ->
        let x = { x with PathName.path = path @ x.PathName.path } in
        match depth x env with
        | None -> None
        | Some (x, d) -> Some (x, d + 1))
  | [] -> None

let bound_name (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t =
  match depth x env with
  | Some (x, d) -> { BoundName.path_name = x; depth = d }
  | None ->
    let message = PathName.pp x ^^ !^ "not found." in
    Error.raise loc (SmartPrint.to_string 80 2 message)

let rec find (x : BoundName.t) (env : 'a t) (open_lift : 'a -> 'a) : 'a =
  let segment =
    try List.nth env x.BoundName.depth with
    | Failure _ -> raise Not_found in
  let rec iterate_open_lift v n =
    if n = 0 then
      v
    else
      iterate_open_lift (open_lift v) (n - 1) in
  let v = Segment.find x.BoundName.path_name segment in
  iterate_open_lift v x.BoundName.depth

let mem (x : PathName.t) (env : 'a t) : bool =
  match depth x env with
  | Some _ -> true
  | None -> false

(** Add a fresh local name beginning with [prefix] in [env]. *)
let fresh (prefix : string) (v : 'a) (env : 'a t) : Name.t * 'a t =
  let prefix_n s n =
    if n = 0 then
      Name.of_string s
    else
      Name.of_string @@ Printf.sprintf "%s_%d" s n in
  let rec first_n (n : int) : int =
    if mem (PathName.of_name [] @@ prefix_n prefix n) env then
      first_n (n + 1)
    else
      n in
  let x = prefix_n prefix (first_n 0) in
  (x, add (PathName.of_name [] x) v env)

let map (env : 'a t) (f : 'a -> 'b) : 'b t =
  List.map (Segment.map f) env

let enter_module (env : 'a t) : 'a t =
  Segment.empty :: env

let leave_module (env : 'a t) (prefix : Name.t -> 'a -> 'a)
  (module_name : Name.t) : 'a t =
  match env with
  | segment1 :: segment2 :: env ->
    Segment.merge segment1 segment2 prefix module_name :: env
  | _ -> failwith "You should have entered in at least one module."

let open_module (env : 'a t) (module_name : Name.t list) : 'a t =
  match env with
  | segment :: env -> Segment.open_module segment module_name :: env
  | _ -> failwith "You should have entered in at least one module."
