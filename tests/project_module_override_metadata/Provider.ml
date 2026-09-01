module Counter : sig
  type t

  val zero : t
  val succ : t -> t
  val pred : t -> t
  val to_int : t -> int
end = struct
  type t = int

  let zero = 0
  let succ value = value + 1
  let pred value = if value = 0 then invalid_arg "pred" else value - 1
  let to_int value = value
end

let one = Counter.succ Counter.zero
let decrement value = Counter.pred value
