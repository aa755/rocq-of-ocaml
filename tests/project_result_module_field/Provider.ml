module type ARGUMENT = sig
  val token : unit
end

module Fixed (Argument : ARGUMENT) = struct
  type t = int

  module Map : sig
    type t

    val empty : t
  end = struct
    type t = int list

    let empty : t = []
  end
end

module DefaultArgument = struct
  let token = ()
end

module Applied = Fixed (DefaultArgument)

module Aliased (Argument : ARGUMENT) = struct
  module Direct = Fixed (Argument)
  module Alias = Direct
end

module Base (Argument : ARGUMENT) = struct
  type t = int

  let identity value = value
end

module Outer (Argument : ARGUMENT) = struct
  module Included = Base (Argument)

  module Namespace = struct
    include Included

    module Repr = Fixed (Argument)
  end
end

module Anonymous (T : sig
  type t
end) =
struct
  let identity (value : T.t) = value
end

module type INPUT = sig
  val value : int
end

module type OUTPUT = sig
  val result : int
end

module Consume
    (Producer : functor (Input : INPUT) -> OUTPUT)
    (Input : INPUT) =
struct
  module Result = Producer (Input)
end
