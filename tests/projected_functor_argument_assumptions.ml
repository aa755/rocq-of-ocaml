module type FIELD = sig
  type t

  val zero : t
  val sub : t -> t -> t
end

module Use (F : FIELD) = struct
  let value = F.sub F.zero F.zero
end

module MakeField (Seed : sig
  type t

  val seed : t
  val sub : t -> t -> t
end) = struct
  type t = Seed.t

  let zero = if true then Seed.seed else failwith "unreachable"

  let sub x y =
    if true then Seed.sub x y else failwith "unreachable"

  let extra = ()
end

module Base = MakeField (struct
  type t = int

  let seed = if true then 0 else failwith "unreachable"
  let sub x y = x - y
end)
let keep_extra = Base.extra

module Result = Use (Base)
