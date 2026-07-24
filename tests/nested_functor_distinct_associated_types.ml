module type TOKEN = sig
  val token : unit
end

module Number (Token : TOKEN) = struct
  module Impl : sig
    type t

    val make : int -> t
  end = struct
    type t = int

    let make value = value
  end

  include Impl

  module Set = Stdlib.Set.Make (struct
    type t = Impl.t

    let compare (_ : t) (_ : t) = 0
  end)
end

module Representation (Token : TOKEN) = struct
  module Impl : sig
    type t

    val make : string -> t
  end = struct
    type t = string

    let make value = value
  end

  include Impl

  let bytes_marker = ()
end

module ConcreteRepresentation (Token : TOKEN) = struct
  module Impl : sig
    type t = private string

    val make : string -> t
  end = struct
    type t = string

    let make value = value
  end

  include Impl
end

module Pair (Token : TOKEN) = struct
  module S = Number (Token)

  module Signed = struct
    include S

    module Repr = Representation (Token)
    module Bytes = ConcreteRepresentation (Token)

    let of_repr (_ : Repr.t) : t = S.make 0
    let of_bytes (_ : Bytes.t) : t = S.make 0
  end
end
