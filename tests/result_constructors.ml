let success = Ok 3
let failure = Error "failure"
let success_function = Stdlib.Result.ok 3
let failure_function = Stdlib.Result.error "failure"

let recover = function
  | Ok value -> value
  | Error _ -> 0

module type RETURN = sig
  type 'a t
  val return : 'a -> 'a t
end

module Use (M : RETURN) = struct
  let wrap value : (int, string) result M.t =
    M.return (Ok value)
end
