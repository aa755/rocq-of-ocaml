module type FIELD = sig
  type t

  val zero : t
end

module Use (M : sig
  module Field : sig
    include FIELD with type t = int

    val one : t
  end

  module Wrapped : sig
    type t = private Field.t

    val make : Field.t -> t
  end
end) =
struct
  let zero = M.Field.zero
  let one = M.Field.one
  let wrapped = M.Wrapped.make one
end
