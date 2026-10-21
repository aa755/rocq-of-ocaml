module Outer (X : sig val initial : int end) = struct
  module State : sig
    type t
    val zero : t
    val value : t -> int
  end = struct
    type t = int
    let zero = X.initial
    let value x = x
  end

  module Run (C : sig val state : State.t end) = struct
    let result = State.value C.state
  end
end

module Wrapper (X : sig val initial : int end) = struct
  module Base = Outer (X)
  include Base

  module Run (C : sig val state : State.t end) = struct
    include Base.Run (C)
  end
end

module Applied = Wrapper (struct let initial = 7 end)
let value = Applied.State.value Applied.State.zero
