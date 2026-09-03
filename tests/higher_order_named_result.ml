module type HOST = sig
  type t
end

module Vm (State : sig
  type t
end) =
struct
  module type SIG = sig
    val execute : State.t -> State.t
  end
end

module State = struct
  type t = int
end

module MakeHost
    (Config : sig end)
    (VmImpl : Vm(State).SIG) =
struct
  type t = State.t

  let internal = 0
end

module Tie
    (State : sig
      type t
    end)
    (HostImpl : functor (Vm : Vm(State).SIG) -> HOST with type t = State.t)
    (Vm : functor (Host : HOST with type t = State.t) -> Vm(State).SIG) =
struct
  let marker = 0
end

module Instantiate
    (Config : sig end)
    (Vm : functor (Host : HOST with type t = State.t) -> Vm(State).SIG) =
struct
  include Tie (State) (MakeHost (Config)) (Vm)
end
