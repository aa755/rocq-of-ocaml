module Impl : sig
  val value : int
  val double : int -> int
  val identity : 'a -> 'a

  module Nested : sig
    val value : int
  end
end = struct
  let value = 7
  let double x = x + x
  let identity x = x

  module Nested = struct
    let value = 11
  end
end

include Impl
