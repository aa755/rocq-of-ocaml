module type ARGUMENT = sig
  val token : unit
end

module Make (A : ARGUMENT) = struct
  type t = int

  let missing : t = assert false
end

module Argument = struct
  let token = ()
end

module Private = Make (Argument)

module Public = struct
  include Private

  let use_again : t = missing
end

module Alias = Public

let through_public = Public.missing
let through_public_call = Public.use_again
let through_alias = Alias.missing
