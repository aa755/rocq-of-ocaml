module type PARAM = sig
  val fallback : string
end

module Make (Param : PARAM) = struct
  module Host = struct
    type t = string
  end

  let initial () : Host.t =
    if true then Param.fallback else assert false
end
