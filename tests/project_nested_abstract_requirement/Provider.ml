module M = struct
  type 'a t = Present of 'a | Missing
end

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
    let mixed () : int M.t * Int32.t = (assert false, assert false)
  end
end
