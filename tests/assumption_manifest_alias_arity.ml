module Bytes = struct
  type t = string
end

module type ARGUMENT = sig
  val token : unit
end

module Make (Argument : ARGUMENT) = struct
  let tails (bytes_values : Bytes.t list) (string_values : string list) =
    let () = Argument.token in
    (List.tl bytes_values, List.tl string_values)
end
