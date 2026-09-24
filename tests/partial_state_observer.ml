module M = struct
  type 'a t = int -> ('a, bool) result * int

  let return value state = (Ok value, state)

  let bind action next state =
    let result, state = action state in
    match result with Ok value -> next value state | Error error -> (Error error, state)

  let fail error state = (Error error, state + 1)
end

module Other = struct
  let step n state = (Ok (n = 0), state)
end

module Machine (Config : sig val count : int end) = struct
  let rec step n : bool M.t =
    if n < 0 then M.fail true
    else if n = 0 then M.return false
    else M.bind (M.return (n - 1)) (fun value -> step value)

  let apply n state = step n state

  let nested n state = (step n) state

  let current : bool M.t = step 0

  let observe_current state = current state

  let within n state : int M.t =
    let result, next_state = step n state in
    match result with
    | Ok _ -> M.return next_state
    | Error error -> M.fail error

  let state_action n : bool M.t = step n

  let total n state = Other.step n state

  let rec run state =
    let result, state = step Config.count state in
    match result with
    | Ok true -> run state
    | _ -> (result, state)
end

module Concrete = Machine (struct let count = 2 end)
