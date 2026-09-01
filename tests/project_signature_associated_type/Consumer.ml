module type SIG = sig
  type 'a t

  val return : 'a -> 'a t
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
end

module type SIG_MONAD = SIG

module Make (M : SIG) = struct
  include M

  let map f x = M.(x >>= fun x -> return (f x))
end

module Make_Monad = Make

module type TRANS = sig
  include SIG

  module Inner : SIG

  val lift : 'a Inner.t -> 'a t
end
