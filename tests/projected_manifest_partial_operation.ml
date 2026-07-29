module type VALUE = sig
  type t

  val optional : t option
end

module Provider (Value : VALUE) = struct
  type t = Value.t

  let optional = Value.optional
  let required () = Option.get optional
end

module Consumer (Value : VALUE) = struct
  module P = Provider (Value)

  let required () =
    P.required ()
end
