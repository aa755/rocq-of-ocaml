module type PARAM = sig
  type t

  val fallback : t
end

module Generated (Param : PARAM) = struct
  type t = Param.t

  let make value : t = if true then value else assert false
end

module Outer (Param : PARAM) = struct
  module Applied = Generated (Param)

  type state = { value : Applied.t }

  let initial = { value = Applied.make Param.fallback }
end
