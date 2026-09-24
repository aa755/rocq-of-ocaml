module State (T : sig type t end) = struct
  type 'a t = T.t -> 'a * T.t
  let return value state = (value, state)
  let bind action next state = let value, state = action state in next value state
end
module Outer (Host : sig type t end) = struct
  module HostState = State (Host)
  module Runner (Config : sig val offset : int end) = struct
    let rec run n = if n = 0 then (Config.offset, n) else run (n - 1)
  end
  let execute n : int HostState.t =
    HostState.bind (HostState.return n) (fun value ->
      let module Local = Runner (struct let offset = value end) in
      let result, state = Local.run value in
      HostState.return (result + state))
end

module Concrete = Outer (struct type t = int end)

let execute_concrete n = Concrete.execute n
