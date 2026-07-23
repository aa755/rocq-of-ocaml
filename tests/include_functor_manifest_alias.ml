module type Empty = sig
  val token : unit
end

module Make (Argument : Empty) = struct
  module Impl : sig
    type t

    val make : int -> t
  end = struct
    type t = int

    let make value = value
  end

  include Impl

  let identity (value : Impl.t) = value
end

module Empty_value = struct
  let token = ()
end

module Base = Make (Empty_value)

module Extended = struct
  include Base

  let round_trip (value : int) : t = identity (make value)
end
