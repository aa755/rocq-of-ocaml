let keep = 1
let drop = 2
let drop_by_suffix = 5
external drop_external : int -> int = "drop_external"

module Nested = struct
  let keep_nested = 3
  let drop_nested = 4
end

module Packed : sig
  val keep_packed : int
  val drop_packed : int
end = struct
  let keep_packed = 6
  let drop_packed = 7
end

include Packed

module Packed_alias = Packed

module Plain = struct
  let keep_plain = 8
  let drop_plain = 9
end

include Plain
