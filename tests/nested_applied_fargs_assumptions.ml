module type VALUE = sig
  type t

  val value : t
end

module Outer (Left : VALUE) = struct
  module Child (Right : VALUE with type t = Left.t) = struct
    let pair = (Left.value, Right.value)
  end
end

module Parent = Outer (struct
  type t = int

  let value = if true then 1 else failwith "unreachable"
end)

module Result = Parent.Child (struct
  type t = int

  let value = if true then 2 else failwith "unreachable"
end)
