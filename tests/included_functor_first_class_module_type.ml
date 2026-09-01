module Base (Ignored : sig end) = struct
  module Set = Set.Make (Int)

  module Map = struct
    let keys () : Set.t = Set.empty
  end
end

module Wrapper (Ignored : sig end) = struct
  include Base (Ignored)

  let marker = ()
end

module Result = Wrapper (struct end)

module Copy = struct
  include Result
end

let keys = Copy.Map.keys ()
