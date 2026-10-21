let to_yojson (x : int) = x
let _ = to_yojson

let kept x = x + 1
let _ = kept
let _ = kept 2

module Nested = struct
  let to_yojson () = 3
  let _ = to_yojson
  let kept = 4
end
