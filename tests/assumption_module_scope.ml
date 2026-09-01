let map = function Some value -> value | None -> assert false

module Base = struct
  let map value = value
end

module Nested : sig
  val map : int -> int
end = struct
  include Base
end

module Partial_base = struct
  let find = function Some value -> value | None -> assert false
end

module Partial_nested : sig
  val find : int option -> int
end = struct
  include Partial_base
end

module type ARGUMENT = sig
  val token : unit
end

module Make (Argument : ARGUMENT) = struct
  module Map = struct
    let find = function Some value -> value | None -> assert false
  end
end

module type KEY = sig
  type t
end

module Keyed (Key : KEY) = struct
  module Map = struct
    type key = Key.t

    let min_binding (entries : (key * 'a) list) : key * 'a =
      match entries with entry :: _ -> entry | [] -> assert false
  end
end

module Int_key = struct
  type t = int
end

module Int_keyed = Keyed (Int_key)

let first_string (entries : (int * string) list) =
  Int_keyed.Map.min_binding entries
