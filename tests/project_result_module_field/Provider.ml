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
