module type ARG = sig
  type left
  type right

  val left_value : left
  val right_value : right
end

module Applied (Arg : ARG) = struct
  module Key = struct
    type t = int

    let compare = Int.compare
  end

  module Set = Set.Make (Key)

  let pair = (Arg.left_value, Arg.right_value)
end

module type PARAM = sig
  val value : int
end

module Outer (Param : PARAM) = struct
  module Local = struct
    type left = int
    type right = string
  end

  module Result = Applied (struct
    type left = Local.left
    type right = Local.right

    let left_value : Local.left = List.hd ([] : Local.left list)
    let right_value : Local.right = Option.get (None : Local.right option)
  end)

  let unrelated_partial value =
    if Param.value = 0 then List.hd value else List.hd value
end
