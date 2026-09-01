module type VALUES = sig
  val text : string
  val number : int
end

module Wrap (Values : VALUES) = struct
  let text = if true then Values.text else assert false
  let number = if true then Values.number else assert false
  let marker = ()
end

module Outer (Values : VALUES) = struct
  module Inner = Wrap (Values)

  module Result = Wrap (struct
    let text = Inner.text
    let number = Inner.number
  end)
end
