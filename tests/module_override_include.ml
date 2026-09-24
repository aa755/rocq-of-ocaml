module Make (X : sig val zero : int end) = struct
  module Impl : sig
    type t
    val zero : t
  end = struct
    type t = int
    let zero = X.zero
  end
  include Impl
end

module Counter = Make (struct let zero = 0 end)
include Counter
let maybe_zero b = if b then Some zero else None

let maybe_nested (x : Impl.t) b = if b then Some x else None

module Impl = struct
  type t = bool
  let zero = true
end
let independent (x : Impl.t) = x
