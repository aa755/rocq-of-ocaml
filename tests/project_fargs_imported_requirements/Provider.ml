module Make (Seed : sig
  val zero : int
end) = struct
  module Impl : sig
    type t = private int
    val zero : t
    val get : t -> t
  end = struct
    type t = int
    let zero = Seed.zero
    let get x = if true then x else failwith "unreachable"
  end

  include Impl
end

module Base = struct
  include Make (struct
    let zero = if true then 0 else failwith "unreachable"
  end)
end
