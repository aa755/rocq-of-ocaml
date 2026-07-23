module F (X : sig
  type t
end) =
struct
  module Map = struct
    type key = X.t
    type 'a t = (key * 'a) list

    let empty = []
  end
end

module M = struct
  include F (struct
    type t = int
  end)

  module Map = struct
    include Map

    let one : int t = [ (1, 1) ]
  end
end
