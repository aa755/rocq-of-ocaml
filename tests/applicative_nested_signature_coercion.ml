module type TYPE = sig
  type t
end

module type INPUT = sig
  type t
  val value : t
end

module Family (T : TYPE) = struct
  module type SIG = sig
    val apply : T.t -> T.t
  end
end

module Consume
    (T : TYPE)
    (Producer : functor (Input : INPUT with type t = T.t) -> Family(T).SIG)
    (Input : INPUT with type t = T.t) =
struct
  let result = Input.value
end

module IntType = struct
  type t = int
end

module Produce (Input : INPUT with type t = int) =
struct
  let apply value = value
  let extra = Input.value
end

module Input = struct
  type t = int
  let value = 42
end

module Applied = Consume (IntType) (Produce) (Input)
