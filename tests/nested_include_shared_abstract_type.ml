module type ARGUMENT = sig
  val token : unit
end

module Make (Argument : ARGUMENT) = struct
  module Impl : sig
    type t

    val make : int -> t
  end = struct
    type t = int

    let make value = value
  end

  include Impl

  let identity (value : t) = value
end

module Outer (Argument : ARGUMENT) = struct
  module S = Make (Argument)

  module Signed = struct
    include S

    let round_trip (value : int) : t = identity (make value)
  end
end

module Argument = struct
  let token = ()
end

module Result = Outer (Argument)

let make_through_alias = Result.Signed.Impl.make
