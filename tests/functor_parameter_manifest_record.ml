module Consumer (M : sig
  module Pair : sig
    type t = { left : int; right : int }
  end
end) = struct
  let make left right = M.Pair.{ left; right }
  let swap value = M.Pair.{ left = value.right; right = value.left }
end

module Actual = struct
  module Pair = struct
    type t = { left : int; right : int }
  end
end

module Applied = Consumer (Actual)

let result = Applied.swap (Applied.make 1 2)
