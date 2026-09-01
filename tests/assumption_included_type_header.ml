module type VALUE = sig
  type t
end

module Make (Value : sig
  type t

  val default : t
end) = struct
  type t = Value.t list

  let marker = 0
end

module Include (Value : VALUE) = struct
  module Argument = struct
    type t = Value.t

    let default : t = assert false
  end

  module Applied = Make (Argument)

  include Applied

  (* The type [t] is projected through a module application whose construction
     requires [Value.t] to be inhabited.  The translated header must retain
     that requirement even though this function body is just the identity. *)
  let identity (value : t) = value
end
