module type BOX = sig
  type t

  val empty : t
end

module type ARGUMENT = sig
  val token : unit
end

module DefaultArgument = struct
  let token = ()
end

module Box (Argument : ARGUMENT) : BOX = struct
  type t = int list

  let empty = []
end

module State = struct
  module Applied = Box (DefaultArgument)
end

module Reexport = struct
  include State

  type contents = Applied.t

  let empty : Applied.t = Applied.empty
end
