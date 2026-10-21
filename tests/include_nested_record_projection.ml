module type BOX = sig
  type t

  val empty : t
end

module Box (X : sig end) : BOX = struct
  type t = int list

  let empty = []
end

module Outer (X : sig end) = struct
  module Nested = struct
    module Box = Box (X)
  end
end

module Reexport (X : sig end) = struct
  include Outer (X)

  let empty = Nested.Box.empty
end
