type t = {value : int}

include struct
  let _ = fun (_ : t) -> ()
end
[@@merlin.hide]

let get x = x.value
