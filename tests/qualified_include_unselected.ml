module Impl : sig
  val value : int
end = struct
  let value = 7
end

include Impl
