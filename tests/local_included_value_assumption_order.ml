module type VALUE = sig
  type t

  val zero : t
  val equal : t -> t -> bool
end

module Container (Value : VALUE) = struct
  module Impl : sig
    type impl = Value.t Iarray.t
    type t = private impl

    val normalize : impl -> t
  end = struct
    type impl = Value.t Iarray.t
    type t = impl

    let normalize (values : impl) =
      let[@rocq.wf] rec last_nonzero i =
        if i >= 0 && Value.equal (Iarray.get values i) Value.zero then
          last_nonzero (i - 1)
        else
          i
      in
      let last = last_nonzero (Iarray.length values - 1) in
      if last = Iarray.length values - 1 then
        values
      else
        Iarray.init (last + 1) (fun i -> Iarray.get values i)
  end

  include Impl

  let init length make = normalize (Iarray.init length make)
end

module Fixed_string : sig
  type t = private string

  val init : (int -> char) -> t
end = struct
  type t = string

  let init make =
    let length = if true then 20 else assert false in
    String.init length make
end

module Plain_include = struct
  include Fixed_string

  let zeros = init (fun _ -> '\x00')
end
