module type Unary = sig
  type 'a t

  val return : 'a -> 'a t
end

module type Binary = sig
  type ('a, 'key) t

  val return : 'a -> ('a, 'key) t
end

module Impl = struct
  type 'a t = 'a

  let return value = value
end

let result = Impl.return 3
