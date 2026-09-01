module type ARGUMENT = sig
  val token : unit
end

module Fixed (Argument : ARGUMENT) = struct
  type t = int

  let missing : int = assert false

  module Map : sig
    type t

    val empty : t
  end = struct
    type t = int list

    let empty : t = []
  end
end

module DefaultArgument = struct
  let token = ()
end

let unwrap_int = function Some value -> value | None -> assert false

(** A nested failure whose result type must be qualified in exported metadata.
*)
module Local_failure = struct
  type t = Token of int

  let unwrap = function Some value -> value | None -> assert false
end

module Partial_base = struct
  let unwrap = function Some value -> value | None -> assert false
end

module Partial_reexport = struct
  include Partial_base
end

let shadowed_unwrap = function Some value -> value | None -> assert false

module Shadowing = struct
  let shadowed_unwrap = shadowed_unwrap
end

let find = function Some value -> value | None -> assert false

module Recursive = struct
  let rec find = function [] -> 0 | _ :: values -> find values
end

module Applied = Fixed (DefaultArgument)

module Aliased (Argument : ARGUMENT) = struct
  module Direct = Fixed (Argument)
  module Alias = Direct
end

module Base (Argument : ARGUMENT) = struct
  type t = int

  let identity value = value
end

module Outer (Argument : ARGUMENT) = struct
  module Included = Base (Argument)

  module Namespace = struct
    include Included
    module Repr = Fixed (Argument)
  end
end

module Anonymous (T : sig
  type t
end) =
struct
  let identity (value : T.t) = value
end

module type INPUT = sig
  val value : int
end

module type OUTPUT = sig
  val result : int
end

module Consume (Producer : functor (Input : INPUT) -> OUTPUT) (Input : INPUT) =
struct
  module Result = Producer (Input)
end

module Nested (OuterArgument : ARGUMENT) = struct
  module Child (InnerArgument : sig
    val value : int
  end) =
  struct
    let value =
      let () = OuterArgument.token in
      InnerArgument.value
  end
end
