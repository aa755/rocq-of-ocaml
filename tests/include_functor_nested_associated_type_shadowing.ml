module Make (Token : sig
  val token : unit
end) =
struct
  type t = int

  module Collection = Stdlib.Set.Make (struct
    type nonrec t = t

    let compare = Int.compare
  end)
end

module Token = struct
  let token = ()
end

module Int_collection = struct
  include Make (Token)
end
