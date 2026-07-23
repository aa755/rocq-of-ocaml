module type MONAD = sig
  type 'a t

  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
end

module Make (M : MONAD) = struct
  type 'a t = 'a M.t

  let return = M.return
  let bind = M.bind
end

module Result (T : sig
  type t
end) =
struct
  module Trans (Inner : MONAD) = struct
    module Inner = Make (Inner)

    include Make (struct
      type 'a t = ('a, T.t) result Inner.t

      let return (value : 'a) : 'a t = Inner.return (Ok value)

      let bind (value : 'a t) (f : 'a -> 'b t) : 'b t =
        Inner.bind value (function
          | Ok value -> f value
          | Error error -> Inner.return (Error error))
    end)
  end
end
