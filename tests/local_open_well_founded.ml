module type DOMAIN = sig
  type t

  val equal : t -> t -> bool
  val zero : t
  val remainder : t -> t -> t
end

module Search (Domain : DOMAIN) = struct
  let run first second =
    let open Domain in
    let rec loop (current : t) (coefficient : t) (next : t)
        (next_coefficient : t) =
      if equal next zero then (coefficient, current)
      else
        loop next next_coefficient (remainder current next) coefficient
    in
    loop first first second second
end
