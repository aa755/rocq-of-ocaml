module Action = struct
  type ('a, 'state) t = 'state -> 'a * 'state
end

module type HOST = sig
  type t
  val call : int -> (int, t) Action.t
end

module VmProtocol (T : sig type t end) = struct
  module type SIG = sig
    val execute : int -> (int, T.t) Action.t
  end
end

module Instantiate
    (T : sig type t end)
    (HostF : functor (Vm : VmProtocol(T).SIG) -> HOST with type t = T.t)
    (VmF : functor (H : HOST with type t = T.t) -> VmProtocol(T).SIG) : sig
  module Host : HOST with type t = T.t
  module Vm : VmProtocol(T).SIG
end = struct
  module rec Host : HOST with type t = T.t = HostF (Vm)
  and Vm : VmProtocol(T).SIG = VmF (Host)
end
