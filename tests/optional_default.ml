let with_default ?(x = 1) y =
  x + y

let omitted = with_default 5
let supplied = with_default ~x:3 5
