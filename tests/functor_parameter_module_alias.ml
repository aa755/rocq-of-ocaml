module Make (P : sig
  val left : int
  val right : int
end) = struct
  module Alias = P

  let sum = Alias.left + Alias.right
end
