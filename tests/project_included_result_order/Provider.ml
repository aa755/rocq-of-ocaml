module Word = struct
  type t = Word of int
  let zero = if true then Word 0 else assert false
end

module Flag = struct
  type t = Flag of bool
  let zero = if true then Flag false else assert false
end

module Comparable (Impl : sig
  type t
  val compare : t -> t -> int
end) = struct
  module Impl = Impl
  let compare = Impl.compare
  module Set = Set.Make (Impl)
end

module Source = struct
  module Key = struct
    include Comparable (struct
      type t = int
      let compare = Int.compare
    end)
  end

  type t = { number : Word.t; flag : Flag.t; members : Key.Set.t }
  let empty =
    let flag = Flag.zero in
    let number = Word.zero in
    { number; flag; members = Key.Set.empty }
end
