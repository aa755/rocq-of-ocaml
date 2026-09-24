module Make (X : sig val zero : int end) = struct
  module Impl : sig type t val zero : t end = struct
    type t = int
    let zero = X.zero
  end
  include Impl
end
module CounterBase = Make (struct let zero = 0 end)
module Counter = struct
  include CounterBase
  let to_int (_ : t) = 0
end
include Counter
let maybe_zero b = if b then Some zero else None
module Exported = struct include Counter end
module Alias = Exported
module Shadowed = struct
  include Counter
  module Impl = struct
    type t = bool
    let zero = true
  end
end
