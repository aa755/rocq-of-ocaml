module type VALUE = sig
  type t
  val value : t
end

module Outer (Left : VALUE) = struct
  let left = Left.value

  module Inner (Right : VALUE) = struct
    let pair = (Left.value, Right.value)
  end
end

module Applied_int =
  Outer (struct
    type t = int
    let value = 1
  end)

module Wrapper (Left : VALUE) = struct
  module Applied = Outer (Left)
end

module Leaf (Value : VALUE) = struct
  let value = Value.value
  let duplicate = Value.value
end

module Container (Left : VALUE) = struct
  module Applied = Leaf (Left)
end

module Included (Left : VALUE) = struct
  include Container (Left)
end

module Abstract_holder (Left : VALUE) = struct
  module Sealed (Right : VALUE) : VALUE = struct
    type t = Left.t * Right.t
    let value = (Left.value, Right.value)
  end
end

module Derived (Value : VALUE) = struct
  include Value
  let retained : t list = [value]
end

module Shadowed_include (Value : VALUE) = struct
  include Derived (Value)
  include Value
end

module Applied_alias_result (Value : VALUE) = struct
  module Local = Derived (Value)
  let retained : Local.t list = Local.retained
end

module Carrier (Value : sig type t end) = struct
  type state = Value.t
  let keep (x : state) = x
end

module Anonymous_alias_result (Value : VALUE) = struct
  module Local = Carrier (struct type t = Value.t end)
  let keep (x : Local.state) = Local.keep x
end
