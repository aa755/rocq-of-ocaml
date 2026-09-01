module Fixed (Width : sig
  val value : int
end) =
struct
  type t = string

  let init f = String.init (Option.get (Some Width.value)) f
  let get value index = String.get value index

  let reverse value =
    init (fun index -> get value (Width.value - index - 1))
end

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
