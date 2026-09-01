module Make (P : sig
  val value : int
end) = struct
  type t = int

  let get () = P.value
end

module Package (P : sig end) = struct
  module Applied = Make (struct
    let value : int = Option.get None
  end)

  module Checked : sig
    type t = int

    val get : unit -> t
  end = struct
    include Applied
  end

  include Checked
end
