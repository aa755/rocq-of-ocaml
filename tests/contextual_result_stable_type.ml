module Stable (X : sig end) = struct
  type t = { value : int }

  let make value : t = { value = List.hd [ value ] }
  let read (record : t) : int = List.hd [ record.value ]
end
