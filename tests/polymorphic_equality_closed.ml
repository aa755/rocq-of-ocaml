type status =
  | Ready
  | Failed of int

let equal_status (x : status) y = x = y
let not_equal_status (x : status) y = x <> y

let equal_int (x : int) y = x = y
let not_equal_string (x : string) y = x <> y
let equal_int_list (x : int list) y = x = y
