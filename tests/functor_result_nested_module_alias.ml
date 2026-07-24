module Derive (Element : sig
  type t

  val compare : t -> t -> int
end) =
struct
  module Bucket = Set.Make (Element)
end

module Fixed (Width : sig
  val width : int
end) =
struct
  module Impl : sig
    type t = private string

    val zero : t
  end = struct
    type t = string

    let zero = String.make Width.width '\000'
  end

  include Impl

  include Derive (struct
    type nonrec t = t

    let compare (left : t) (right : t) =
      String.compare (left :> string) (right :> string)
  end)

  let empty_bucket : Bucket.t = Bucket.empty
end

module Width20 = struct
  let width = 20
end

module B20 = struct
  include Fixed (Width20)
end

module Namespace = struct
  module Address = struct
    include B20
  end
end

module Chain = Namespace

module type PARAM = sig
  val enabled : bool
end

module Make (Param : PARAM) = struct
  module Address = Chain.Address

  let zero : Address.t = Address.zero
  let empty_bucket : Address.Bucket.t = Address.Bucket.empty
  let enabled = Param.enabled
end

module Reexport (Param : PARAM) = struct
  module Instantiation = Fixed (Width20)
  module Host = Instantiation

  let enabled = Param.enabled
end
