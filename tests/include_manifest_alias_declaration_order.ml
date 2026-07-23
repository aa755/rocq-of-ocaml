module type CORE = sig
  type 'a t

  val return : 'a -> 'a t
end

module Extend (Monad : CORE) = struct
  include Monad
end

module type WITH_GET = sig
  include CORE

  val get : int t
end

module Base = struct
  type 'a t = 'a option

  let return (value : 'a) : 'a t = Some value
  let get : int t = Some 0
end

module Make (Monad : WITH_GET) = struct
  include Monad
  include Extend (Monad)
end

module Result = struct
  include Make (Base)
end
