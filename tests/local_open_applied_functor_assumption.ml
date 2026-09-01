module type ELEMENT = sig
  type t

  val zero : t
end

module Operations (Element : ELEMENT) = struct
  let get () =
    if true then Element.zero else failwith "unreachable"
end

module Nested_operations (Element : ELEMENT) = struct
  module Impl : sig
    type t = private Element.t

    val get : unit -> t
  end = struct
    type t = Element.t

    let get () =
      if true then Element.zero else failwith "unreachable"
  end

  include Impl
end

module Extension
    (Element : ELEMENT)
    (Modulus : sig
      val modulus : Element.t
    end) =
struct
  let value = Modulus.modulus
end

module Concrete = struct
  type t = int

  let zero = 0
end

let read () =
  let open Operations (Concrete) in
  get ()

let read_nested () =
  let open Nested_operations (Concrete) in
  Impl.get ()

module Result = struct
  include
    Extension
      (Concrete)
      (struct
        let modulus =
          let open Operations (Concrete) in
          get ()
      end)
end
