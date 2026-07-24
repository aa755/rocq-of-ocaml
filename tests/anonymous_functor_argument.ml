module First (T : sig
  type t
end) =
struct
  let id (x : T.t) = x
end

module Second (T : sig
  type t
end) =
struct
  let id (x : T.t) = x
end

module First_int = First (struct
  type t = int
end)

module Second_bool = Second (struct
  type t = bool
end)

module Interface (H : sig
  type t
end) =
struct
  module type S = sig
    val get : H.t
  end
end

module type RESULT = sig
  val token : unit
end

module Consumer
    (T : sig
      type t
    end)
    (F : functor (X : Interface(T).S) -> RESULT)
    (X : Interface(T).S) =
struct
  module Applied = F (X)
end
