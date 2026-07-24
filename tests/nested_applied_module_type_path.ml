module type TYPE = sig
  type t
end

module Identity (T : TYPE) = struct
  type t = T.t

  let identity (value : t) = value
end

module Int_type : TYPE = struct
  type t = int
end

module Nested = struct
  module M = Identity (Int_type)
end

let nested_identity (value : Nested.M.t) : Nested.M.t =
  Nested.M.identity value
