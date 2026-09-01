module type INNER = sig
  type t

  val zero : t
end

module type RICH_INNER = sig
  include INNER

  val extra : bool
end

module type OUTER = sig
  module Inner : INNER

  val use : Inner.t -> int
end

module type RICH_OUTER = sig
  module Inner : RICH_INNER

  val use : Inner.t -> int
  val extra : bool
end

module RichInner : RICH_INNER = struct
  type t = int

  let zero = 0
  let extra = true
end

module Rich = struct
  module Inner = RichInner

  let use (_ : Inner.t) = 0
  let extra = true
end

let unpack (module M : OUTER) = M.use M.Inner.zero
let result = unpack (module Rich)
