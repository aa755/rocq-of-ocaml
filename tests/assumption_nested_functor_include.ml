module type ARG = sig
  val token : unit
end

module Make (Argument : ARG) = struct
  let trigger : unit = assert false

  module Nested = struct
    let use () : unit =
      let () = Argument.token in
      trigger
  end
end

module Instantiate (Argument : ARG) = struct
  include Make (Argument)
end
