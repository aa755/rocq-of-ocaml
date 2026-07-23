module Sequence = struct
  type 'a node = Nil | Cons of 'a
  type 'a t = unit -> 'a node
end

module type ELEMENT = sig
  type t
end

module Make (Element : ELEMENT) =
struct
  module Nested = struct
    include Sequence
  end

  let witness = 0
end

module Make_stable = Make

module Wrap (Element : ELEMENT) =
struct
  include Make_stable (Element)
end
