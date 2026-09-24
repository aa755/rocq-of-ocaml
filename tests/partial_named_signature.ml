module Action = struct
  type ('a, 'state) t = 'state -> 'a * 'state
end
module State (T : sig type t end) = struct
  type 'a t = ('a, T.t) Action.t
  let return value state = (value, state)
  let bind action next state = let value, state = action state in next value state
end
module type HOST = sig
  type t
  val call : int -> (int, t) Action.t
end
module Vm (T : sig type t end) = struct
  module type SIG = sig
    val execute : int -> (int, T.t) Action.t
  end
end
module Engine (Host : HOST) = struct
  module HostState = State (Host)
  let rec run n = if n = 0 then n else run (n - 1)
  let execute n : (int, Host.t) Action.t =
    HostState.bind (HostState.return n) (fun value ->
      let result = run value in
      HostState.return result)
end
module Host (T : sig type t end) (Vm : Vm(T).SIG) = struct
  type t = T.t
  let call n : (int, t) Action.t = Vm.execute n
end

module Connect (Initial : HOST) = struct
  module Execution : Vm(Initial).SIG = Engine (Initial)
  module Callback : HOST with type t = Initial.t = Host (Initial) (Execution)
end

module TotalProtocol (T : sig type t end) = struct
  module type SIG = sig
    val execute : int -> (int, T.t) Action.t
  end
end

module type PURE = sig
  val step : int -> int
end

module UsePure (P : PURE) = struct
  let consume n =
    let answer = P.step n in
    answer + 1
end
