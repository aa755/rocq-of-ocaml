module type ARGUMENT = sig
  val value : int
end

module Operations (Argument : ARGUMENT) = struct
  let get = Argument.value
  let increment x = x + 1
end

open Operations (struct
  let value = 41
end)

let read () = increment get
