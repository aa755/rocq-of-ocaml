module F (X : sig
  val value : int
end) =
struct
  module Impl : sig
    type t = int

    val value : t
  end = struct
    type t = int

    let value = X.value
  end

  include Impl
end

module Applied = struct
  include F (struct
    let value = 7
  end)
end
