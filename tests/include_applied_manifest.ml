module type FIELD = sig
  type t

  val one : t
end

module Ring (Field : FIELD) = struct
  type t = Field.t list
end

module Include_applied_manifest
    (Field : FIELD)
    (Modulus : sig
      val modulus : Ring (Field).t
    end) =
struct
  include Modulus
end

module Base = struct
  type t = int

  let one = 1
end

module Result = struct
  include
    Include_applied_manifest
      (Base)
      (struct
        let modulus = [ Base.one ]
      end)
end
