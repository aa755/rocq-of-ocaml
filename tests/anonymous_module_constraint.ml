module Base = struct
  let x = 1
end

module Wrapped : sig
  include module type of Base

  val y : int
end = struct
  include Base

  let y = 2
end

include Wrapped

module Hidden : sig
  type t = private string

  val make : string -> t
end = struct
  type t = string

  let make value = value
end
