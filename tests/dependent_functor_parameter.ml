module type TYPE = sig
  type t
end

module Box (Value : TYPE) = struct
  type t = Value.t
  let id (value : t) = value
end

module Consume
    (Value : TYPE)
    (Input : sig
      val value : Box(Value).t
    end) =
struct
  module Value_box = Box (Value)
  let result = Value_box.id Input.value
end

module Int_value = struct
  type t = int
end

module Input = struct
  let value = 42
end

module Result = Consume (Int_value) (Input)

let result = Result.result

module Variant (Value : TYPE) = struct
  type t = Point of Value.t | Infinity
  let infinity = Infinity
end

module Int_variant = Variant (Int_value)

let point = Int_variant.Point 42

let point_value = function
  | Int_variant.Point value -> value
  | Int_variant.Infinity -> 0
