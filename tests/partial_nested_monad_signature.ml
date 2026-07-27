module type MONAD = sig
  type 'a t

  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
end

module Make (M : MONAD) = struct
  module Seq = struct
    let rec sequence values =
      match values () with
      | Seq.Nil -> M.return Seq.empty
      | Seq.Cons (value, rest) ->
          M.bind value (fun value ->
              M.bind (sequence rest) (fun rest ->
                  M.return (Seq.cons value rest)))
  end
end

module Identity = struct
  type 'a t = 'a

  let return value = value
  let bind value body = body value
end

module State (T : sig
  type t
end)
(Inner : MONAD) =
struct
  type state = T.t
  module Inner = Inner

  module M = struct
    type 'a t = state -> ('a * state) Inner.t

    let return value state = Inner.return (value, state)

    let bind computation body state =
      Inner.bind (computation state) (fun (value, state) -> body value state)

    let ( >>= ) = bind

    include Make (struct
      type nonrec 'a t = 'a t

      let return = return
      let bind = bind
    end)
  end
end

module StateInt =
  State
    (struct
      type t = int
    end)
    (Identity)

module type PARAM = sig
  val enabled : bool
end

module Instantiate (Param : PARAM) = struct
  module Host = struct
    module M = StateInt.M
  end

  let enabled = Param.enabled
end

module Package (Param : PARAM) = struct
  module Instantiation = Instantiate (Param)
  module Host = Instantiation.Host
  let enabled = Instantiation.enabled
end
