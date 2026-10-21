let excluded x = x
let _ = excluded

let kept x = x + 1
let _ = kept
let _ = kept 2

module Nested = struct
  let excluded () = 3
  let _ = excluded
  let kept = 4
end
