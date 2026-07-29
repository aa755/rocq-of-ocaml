module type PARAMS = sig
  val enabled : bool
end

module type HOST = sig
  val initial : unit
end

module type VM = sig
  val execute : unit -> int
end

module Make_vm (Params : PARAMS) (Host : HOST) = struct
  type address = int

  let invalid_address () : address = assert false
  let execute () = invalid_address ()
end

module Instantiate (Vm : functor (Host : HOST) -> VM) = struct
  module Host = struct
    let initial = ()
  end

  module Vm = Vm (Host)
end

module Apply (Params : PARAMS) = struct
  module Result = Instantiate (Make_vm (Params))
end
