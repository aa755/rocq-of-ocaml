module Complex (Field : sig
  type t

  val zero : t
end) = struct
  type t = { re : Field.t; im : Field.t }

  let zero = { re = Field.zero; im = Field.zero }
  let swap value = { re = value.im; im = value.re }
end

module Int_field = struct
  type t = int

  let zero = 0
end

module Applied = Complex (Int_field)

let components (value : Applied.t) = (value.re, value.im)
let result = Applied.swap Applied.zero
