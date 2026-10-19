let min_int32 = -2147483648l
let max_int32 = 2147483647l
let min_int64 = -9223372036854775808L
let max_int64 = 9223372036854775807L
let unsigned_int64_literal = 0xffffffffffffffffL
let min_nativeint = -9223372036854775808n
let max_nativeint = 9223372036854775807n

let classify = function
  | -9223372036854775808L -> 1
  | 9223372036854775807L -> 2
  | _ -> 3
