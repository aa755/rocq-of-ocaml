module type ARGUMENT = sig
  val token : unit
end

module Make (Argument : ARGUMENT) = struct
  module Impl : sig
    type t

    val optional : (int -> t) option
  end = struct
    type t = int

    let optional =
      let () = Argument.token in
      Some (fun value -> value)
  end

  include Impl
end

module Outer (Argument : ARGUMENT) = struct
  module S = Make (Argument)

  module Public = struct
    include S

    let get = Option.get S.optional
  end
end
