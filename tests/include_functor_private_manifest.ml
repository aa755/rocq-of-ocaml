module Derive (T : sig
  type t

  val compare : t -> t -> int
end) =
struct
  module Set = Set.Make (T)
end

module Make (Argument : sig
  val token : unit
end) =
struct
  module Impl : sig
    type t = private string

    val make : string -> t
  end = struct
    type t = string

    let make value = value
  end

  include Impl

  include Derive (struct
    type nonrec t = t

    let compare (left : t) (right : t) =
      String.compare (left :> string) (right :> string)
  end)
end

module Argument = struct
  let token = ()
end

module Value = struct
  include Make (Argument)
end
