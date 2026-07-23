module Lens = struct
  type ('a, 'b) t = {
    get : 'a -> 'b;
    set : 'b -> 'a -> 'a;
  }
end

module type SIG = sig
  type 'a t

  val return : 'a -> 'a t
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
end

module type SIG_MONAD = SIG

module Make (M : SIG) = struct
  include M

  let ( let$ ) x f = M.(x >>= f)
end

module Make_Monad = Make

module Identity = struct
  module Impl = struct
    type 'a t = 'a

    let return x = x
    let ( >>= ) x f = f x
  end

  include Impl
  include Make (Impl)
end

module State (T : sig
  type t
end) =
struct
  type state = T.t

  module type SIG = sig
    include SIG

    val get : state t
    val put : state -> unit t
  end

  module Make (S : SIG) = struct
    include S
    include Make (S)

    let update (f : state -> state) : unit t =
      get >>= fun state -> put (f state)

    let ( := ) (lens : (state, 'a) Lens.t) (value : 'a) =
      let$ state = get in
      put (lens.set value state)

    let ( ! ) (lens : (state, 'a) Lens.t) : 'a t =
      let$ state = get in
      return (lens.get state)

    let update_field (lens : (state, 'a) Lens.t) (f : 'a -> 'a) : unit t =
      let$ value = !lens in
      lens := f value
  end
end

module Result (T : sig
  type t
end) =
struct
  type error = T.t

  module type SIG = sig
    include SIG_MONAD

    val fail : error -> 'a t
  end

  module Make (S : SIG) = struct
    include S
    include Make_Monad (S)
  end
end

module Result_state (T : sig
  type state
  type error
end) =
struct
  open T

  module State = State (struct
    type t = state
  end)

  module Result = Result (struct
    type t = error
  end)

  module type SIG = sig
    include SIG

    val get : state t
    val put : state -> unit t
    val fail : error -> 'a t
  end

  module Make (S : SIG) = struct
    include S
    include Make (S)
    include State.Make (S)
    include Result.Make (S)
  end

  module Trans (Inner : SIG_MONAD) = struct
    module Inner = Make_Monad (Inner)

    include Make (struct
      type 'a t = state -> (('a, error) result * state) Inner.t

      let return (value : 'a) : 'a t =
       fun state ->
        Inner.return (Ok value, state)

      let ( >>= ) (computation : 'a t) (next : 'a -> 'b t) =
       fun state ->
        Inner.(
          let$ result, state = computation state in
          match result with
          | Error error -> Inner.return (Error error, state)
          | Ok value -> next value state)

      let get : state t =
       fun state ->
        Inner.return (Ok state, state)

      let put (state : state) : unit t =
       fun _ ->
        Inner.return (Ok (), state)

      let fail (error : error) : 'a t =
       fun state ->
        Inner.return (Error error, state)
    end)
  end

  include Trans (Identity)

  let update (f : state -> state) : unit t =
   fun state ->
    (Ok (), f state)

  let ( ! ) (lens : (state, 'a) Lens.t) : 'a t =
   fun state ->
    (Ok (lens.get state), state)

  let ( := ) (lens : (state, 'a) Lens.t) (value : 'a) : unit t =
   fun state ->
    (Ok (), lens.set value state)

  let update_field (lens : (state, 'a) Lens.t) (f : 'a -> 'a) : unit t =
   fun state ->
    (Ok (), lens.set (f (lens.get state)) state)
end
