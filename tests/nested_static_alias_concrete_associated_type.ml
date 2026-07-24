module type PARAM = sig
  val value : int
end

module Key = struct
  type t = int

  let compare = Int.compare
end

module GlobalAddress = struct
  type t = int

  module Set = Set.Make (Key)
end

module Inner (Param : PARAM) = struct
  module Address = GlobalAddress

  let empty = Address.Set.empty
  let value = Param.value
end

module Outer (Param : PARAM) = struct
  module Vm = Inner (Param)
end

module Param = struct
  let value = 42
end

module Result = Outer (Param)

let empty = Result.Vm.empty
