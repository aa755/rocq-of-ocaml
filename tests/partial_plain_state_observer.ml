module M = struct
  type 'a t = int -> 'a * int
  let return value state = (value, state)
  let bind action next state = let value, state = action state in next value state
  let advance state = ((), state + 1)
end

module Machine (Config : sig val count : int end) = struct
  let rec step n : int M.t =
    if n = 0 then M.return n
    else M.bind M.advance (fun () -> step (n - 1))

  let read n state = step n state

  let in_monad n state : int M.t =
    let _, state = step n state in
    M.return state

  let rec run state =
    let value, state = step Config.count state in
    if value = 0 then (value, state) else run state
end

module Concrete = Machine (struct let count = 2 end)
