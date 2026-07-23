module Option = struct
  type 'a t = 'a option

  let none = None
  let return value = Some value
end

module Make (Token : sig
  val token : unit
end) =
struct
  module Option = struct
    include Option
  end
end

module Token = struct
  let token = ()
end

module Result = struct
  include Make (Token)
end
