(** Open *)

module M = struct
  let f _ = failwith "failure"
end

module N = struct
  let f _ = assert false
  let x = try f () with Assert_failure _ -> ()
  open M
  let y = try f () with Failure _ -> ()
end

let b = try N.f () with Assert_failure _ -> ()
open N
let b' = try N.f () with Assert_failure _ -> ()

let x = 15

module A = struct
  let x _ = assert false
end

module B = struct
  let a = x (* Toplevel x *)
  open A
  let b = x (* A.x *)
  let x _ = failwith "failure"
  let c = x (* B.x *)
end

module C = struct
  let a = x (* Toplevel x *)
  let x _ = failwith "failure"
  let b = x (* C.x *)
  open A
  let c = x (* A.x *)
end

module D = struct
  module A = struct
    let a = 2
  end
  let b = x (* Toplevel x *)
  open A
  let c = a (* D.A.a *)
  let d = x (* Toplevel x *)
end
