open Project.Provider

module Outer (Width : sig
  val value : int
end) =
struct
  module Inner = struct
    module Repr = Fixed (Width)

    let reverse (value : Repr.t) = Repr.reverse value
  end
end

module Result = Outer (struct
  let value = 32
end)

let reverse = Result.Inner.reverse
