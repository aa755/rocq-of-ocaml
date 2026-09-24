module M = struct
  type 'a t = int -> 'a * int
  let return value state = (value, state)
  let bind action next state = let value, state = action state in next value state
  let advance state = ((), state + 1)
end

module N = struct
  type 'a t = int -> 'a * int
end

let lift (action : 'a M.t) : 'a N.t = action

module Make (Config : sig val count : int end) = struct
  let rec step n : int M.t =
    if n = 0 then M.return n
    else M.bind M.advance (fun () -> step (n - 1))

  let current : int M.t = step Config.count

  let choose flag ~(otherwise : int M.t) : int M.t =
    if flag then current else otherwise
end

module Default = Make (struct let count = 2 end)
module Included = struct include Default end
