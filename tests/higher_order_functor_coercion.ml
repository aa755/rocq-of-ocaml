module type INPUT = sig
  val value : int
end

module type OUTPUT = sig
  val result : int
end

module Produce (Input : sig
  val value : int
end) =
struct
  module Memory : sig
    type t

    val fallback : t
  end = struct
    type t = int

    let fallback = Input.value
  end

  let result =
    let (_ : Memory.t) = assert false in
    Input.value

  let extra = Input.value + 1
end

module Consume
    (Producer : functor (Input : INPUT) -> OUTPUT)
    (Input : INPUT) =
struct
  module Result = Producer (Input)
end

module Concrete = struct
  let value = 41
end

module Applied = Consume (Produce) (Concrete)
