module type ARGUMENT = sig
  val value : int
end

module Operations (Argument : ARGUMENT) = struct
  let get = Argument.value
  let ( let$ ) value continuation = continuation value
end

module Concrete = struct
  let value = 41
end

let read () =
  let open Operations (Concrete) in
  let$ value = get in
  value + 1

let read_via_local_module () =
  let module Applied = Operations (Concrete) in
  Applied.get
