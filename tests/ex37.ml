(** Include modules *)

module A = struct
  let a = 5

  let c x = failwith x
end

include A

let b = a + 2

let d b = if b then c "true" else c "false"
