module type VALUE = sig
  type t

  val value : t
end

module Outer (Left : VALUE) = struct
  let left = Left.value

  module Child (Right : VALUE) = struct
    let pair = (Left.value, Right.value)
  end
end

module Use (Value : VALUE) = struct
  module Applied = Outer (Value)
  module Result = Applied.Child (Value)
end
