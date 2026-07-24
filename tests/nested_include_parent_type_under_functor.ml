module type S = sig
  type 'a t
end

module Make (M : S) = struct
  include M

  module List = struct
    type 'a t = 'a list

    let lift (value : 'a M.t) : 'a M.t = value
  end
end

module Outer (T : sig
  type error
end) =
struct
  module Trans (Inner : S) = struct
    include Make (struct
      type 'a t = ('a, T.error) result Inner.t
    end)
  end
end
