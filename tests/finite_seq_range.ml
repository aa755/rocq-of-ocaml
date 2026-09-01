module Local = struct
  include Seq
end

module type ARG = sig
  val marker : int
end

module Make (Argument : ARG) = struct
  let marker = Argument.marker

  module Seq = struct
    type 'a t = 'a Stdlib.Seq.t

    let synthetic_signature_identity (values : 'a t) = values
  end
end

let identity (values : 'a Local.t) = values
let bounded count start = Seq.take count (Seq.ints start)

let bounded_iterate count step start =
  Seq.take count (Seq.iterate step start)
