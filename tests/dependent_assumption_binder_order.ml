module type VALUE = sig
  type t
end

module Make (Value : sig
  type t

  val default : t
  val gate : bool
end) = struct
  type t = Value.t

  let default = Value.default
  let copied_gate = Value.gate
end

module Base = struct
  module Argument = struct
    type t = int

    let default : t = assert false
    let gate = if true then true else assert false
  end

  include Make (Argument)

  let one : t = if true then default else assert false
end

module Extension
    (Field : sig
      type t

      val one : t
    end)
    (Modulus : sig
      val modulus : Field.t
    end) =
struct
  let value = Modulus.modulus
end

module Result = struct
  include
    Extension
      (Base)
      (struct
        let modulus = Base.one
      end)
end
