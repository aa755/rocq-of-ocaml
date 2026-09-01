module type DOMAIN = sig
  type t

  val equal : t -> t -> bool
  val zero : t
  val remainder : t -> t -> t
end

module Outer (First : DOMAIN) = struct
  module Search (Second : DOMAIN) = struct
    let run first second =
      let rec loop (current : Second.t) (next : Second.t) =
        if Second.equal next Second.zero then current
        else loop next (Second.remainder current next)
      in
      let _ = First.zero in
      loop first second
  end
end
