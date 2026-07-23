module type Input = sig
  type t
  val value : t
end

module type Output = sig
  type t
  val pair : t
end

module Outer (X : Input) = struct
  let outer_value = X.value

  module F (Y : Input) : Output with type t = X.t * Y.t = struct
    type t = X.t * Y.t
    let pair = (X.value, Y.value)
  end
end
