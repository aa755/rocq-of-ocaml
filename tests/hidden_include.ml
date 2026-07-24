type t = {value : int}

include struct
  let _ = fun (_ : t) -> ()
end
[@@merlin.hide]

include struct
  let generated value = value + 1
end
[@@merlin.hide]

let get x = x.value
let generated_result = generated 41
