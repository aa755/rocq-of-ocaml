module type VALUE = sig
  type t

  val optional : t option
end

module Read (Value : VALUE) = struct
  let required =
    Value.(Option.get optional)
end
