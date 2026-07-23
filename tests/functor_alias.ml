module type Input = sig
  type t

  val default : t
end

module Make (Value : Input) = struct
  type t = Value.t option

  let default = Some Value.default
end

module Make_alias = Make

module Value = struct
  type t = int

  let default = 3
end

module Result = Make_alias (Value)

let result : Result.t = Result.default
