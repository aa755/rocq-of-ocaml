module type Input = sig
  type t

  val value : t
end

module Outer (X : Input) = struct
  module type Local = sig
    type 'a t

    val inject : X.t -> 'a -> 'a t
  end

  module Make (M : Local) = struct
    include M
  end
end

module Inline (T : sig
  type t

  val other : t
end) =
struct
  let result = T.other
end
