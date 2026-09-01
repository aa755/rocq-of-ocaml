module type WIDTH = sig
  val bytes : int
end

module Fixed (Width : WIDTH) = struct
  type t = string

  let identity (value : t) = value
end

module Pair (Width : WIDTH) = struct
  module Signed = struct
    module Repr = Fixed (Width)

    let of_repr (value : Repr.t) = Repr.identity value
  end
end

module Width = struct
  let bytes = 32
end

module Result = Pair (Width)

let result = Result.Signed.of_repr "value"
