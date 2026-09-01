module type ELEMENT = sig
  type t

  val zero : t
end

module Operations (Element : ELEMENT) = struct
  let get () =
    if true then Element.zero else failwith "unreachable"

  let check () =
    if true then true else failwith "unreachable"
end

module Extension
    (Element : ELEMENT)
    (Modulus : sig
      val modulus : Element.t
    end) =
struct
  include Operations (Element)

  let value = Modulus.modulus
end

module Packaged (Element : ELEMENT) = struct
  module Applied =
    Extension
      (Element)
      (struct
        let modulus =
          let open Operations (Element) in
          if check () then Element.zero else Element.zero
      end)

  include Applied
end
