module Outer (X : sig type t val initial : t end) = struct
  module Memory : sig
    type t
    val empty : t
  end = struct
    type t = X.t list
    let empty : t = []
  end

  module Run (C : sig val state : Memory.t end) = struct
    let get () = C.state
    let missing () : Memory.t = assert false
    let indirect () = (assert false : Memory.t -> int) C.state
  end
end

module Wrapper (X : sig type t val initial : t end) = struct
  module Base = Outer (X)
  include Base

  module Run (C : sig val state : Memory.t end) = struct
    include Base.Run (C)
  end
end
