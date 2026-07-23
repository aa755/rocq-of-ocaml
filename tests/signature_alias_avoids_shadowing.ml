module type BASE = sig
  type 'a t
  val return : 'a -> 'a t
end

module Extend (M : BASE) = struct
  include M
  let map f x = M.return (f x)
end

module type BASE_STABLE = BASE
module Extend_stable = Extend

module Nested = struct
  module type BASE = sig
    include BASE_STABLE
    val get : int t
  end

  module Make (M : BASE) = struct
    include Extend_stable (M)
  end
end
