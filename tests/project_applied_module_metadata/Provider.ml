module type VALUE = sig
  type t

  val value : t
end

module Outer (Left : VALUE) = struct
  type t = Left.t

  let get flag = if flag then Left.value else assert false

  module Child (Right : VALUE) = struct
    let pair = (Left.value, Right.value)
  end
end

module Int_value = struct
  type t = int

  let value = 42
end

module Applied = Outer (Int_value)
