module Fixed (Width : sig
  val width : int
end) = struct
  let width : int = if true then Width.width else assert false

  module Impl : sig
    type t = private string

    val init : (int -> char) -> t
  end = struct
    type t = string

    let init byte_i : t = String.init width byte_i
  end

  include Impl
end
