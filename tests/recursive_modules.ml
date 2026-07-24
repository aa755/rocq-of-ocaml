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

  let two_is_even = First.even 2
end

module MakeA (Other : B) = struct
  let rec even n = n = 0 || Other.odd (n - 1)
end

module MakeB (Other : A) = struct
  let rec odd n = n <> 0 && Other.even (n - 1)
end

module Instance = Instantiate (MakeA) (MakeB)

let four_is_even = Instance.First.even 4

module type TYPE = sig
  type t
end

module Box (T : TYPE) =
struct
  module type S = sig
    val run : T.t -> T.t
  end
end

module RecursiveResult
    (T : TYPE)
    (MakeWorker : functor (X : TYPE with type t = T.t) -> Box(T).S) : sig
  module Worker : Box(T).S
end =
struct
  module rec Worker : Box(T).S = MakeWorker (T)
end
