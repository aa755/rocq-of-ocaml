module type VALUE = sig
  type t

  val zero : t
end

module Wrap (Input : VALUE) = struct
  type t = Input.t

  let zero = Input.zero
  let pair = (zero, zero)
end

module Int_value = struct
  type t = int

  let zero = 0
end

module State = struct
  module TransactionState = struct
    module M = Wrap (Int_value)
  end
end

module M = State.TransactionState.M

module Use (M : VALUE) = struct
  type t = M.t

  let zero = M.zero
end

module Result = Use (M)
let result : int = Result.zero
