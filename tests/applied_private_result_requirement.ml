module type VALUE = sig
  type t
end

module Make (Value : VALUE) = struct
  module Impl : sig
    type impl = Value.t list
    type t = private impl

    val of_impl : impl -> t
  end = struct
    type impl = Value.t list
    type t = impl

    let of_impl value = value
  end

  include Impl

  let impossible () : impl = assert false
  let expose (value : t) = (value :> impl)
end

module Use (Value : VALUE) = struct
  module Applied = Make (Value)

  let use () = Applied.impossible ()
end

module Include (Value : VALUE) = struct
  module Applied = Make (Value)
  include Applied

  let identity (value : t) = value
end
