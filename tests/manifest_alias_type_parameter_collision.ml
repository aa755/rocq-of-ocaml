module type BINARY = sig
  type ('a, 'key) t

  val inject : 'a -> ('a, 'key) t
end

module Make (M : BINARY) = struct
  include M

  let lift (f : 'acc -> 'item -> ('acc, 't) M.t) = f
end
