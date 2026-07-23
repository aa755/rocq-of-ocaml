module type A = sig
  val even : int -> bool
end

module type B = sig
  val odd : int -> bool
end

module Instantiate
    (MakeA : functor (Other : B) -> A)
    (MakeB : functor (Other : A) -> B) =
struct
  module rec First : A = MakeA (Second)
  and Second : B = MakeB (First)
end

module MakeA (Other : B) = struct
  let rec even n = n = 0 || Other.odd (n - 1)
end

module MakeB (Other : A) = struct
  let rec odd n = n <> 0 && Other.even (n - 1)
end

module Instance = Instantiate (MakeA) (MakeB)

let four_is_even = Instance.First.even 4
