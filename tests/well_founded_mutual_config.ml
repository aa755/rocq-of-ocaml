let unwrap = function Some value -> value | None -> assert false

let rec first value =
  if value = 0 then unwrap (Some true) else second (value - 1) = 0

and second value =
  if value = 0 then 0 else if first (value - 1) then value else 0
