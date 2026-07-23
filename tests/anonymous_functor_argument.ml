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
