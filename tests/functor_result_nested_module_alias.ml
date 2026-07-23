module Namespace = struct
  module Address = struct
    let zero = 0
  end
end

module Chain = Namespace

module type PARAM = sig
  val enabled : bool
end

module Make (Param : PARAM) = struct
  module Address = Chain.Address

  let zero = Address.zero
  let enabled = Param.enabled
end
