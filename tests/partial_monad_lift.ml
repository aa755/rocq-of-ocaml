module HostState = struct
  type 'a t = int -> 'a * int
  let return value state = (value, state)
  let bind action next state = let value, state = action state in next value state
end

module MachineState = struct
  type 'a t = int * bool -> 'a * (int * bool)
  let return value state = (value, state)
  let bind action next state = let value, state = action state in next value state
end

module Host = struct
  let rec run n : int HostState.t =
    if n = 0 then HostState.return n
    else HostState.bind (HostState.return (n - 1)) (fun value -> run value)
end

module Other = struct
  let lift n = n + 1
end

module Use (Config : sig val trace : bool end) = struct
  let lift (action : 'a HostState.t) : 'a MachineState.t =
    let _ = Config.trace in
    fun (host, flag) ->
      let value, host = action host in
      (value, (host, flag))

  let execute n : int MachineState.t =
    MachineState.bind (lift (Host.run n)) (fun value ->
      MachineState.return (Other.lift value))

  let total n : int MachineState.t = lift (HostState.return n)
end

module Concrete = Use (struct let trace = false end)
