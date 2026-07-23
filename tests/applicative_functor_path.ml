module Outer (T : Stdlib.Set.OrderedType) = struct
  module Set = Stdlib.Set.Make (T)

  let singleton_and_mem (x : T.t) : bool =
    let values : Set.t = Set.singleton x in
    Set.mem x values
end

module Int_order = struct
  type t = int
  let compare left right = left - right
end

module Applied = Outer (Int_order)

let contains_one = Applied.singleton_and_mem 1

module Anonymous_outer (T : sig
  type t
  val compare : t -> t -> int
end) =
struct
  module Set = Stdlib.Set.Make (T)

  let singleton_and_mem (x : T.t) : bool =
    let values : Set.t = Set.singleton x in
    Set.mem x values
end
