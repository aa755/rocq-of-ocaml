module Outer (T : sig type t end) = struct
  module type SIG = sig
    val get : T.t
  end

  module Copy (M : SIG) : SIG = struct
    let get = M.get
  end
end
