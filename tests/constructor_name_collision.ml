module Status = struct
  type t =
    | Success
    | Failure
    | Stack_overflow
    | Ok
    | Error

  let to_string = function
    | Success -> "success"
    | Failure -> "failure"
    | Stack_overflow -> "stack overflow"
    | Ok -> "ok"
    | Error -> "error"
end
