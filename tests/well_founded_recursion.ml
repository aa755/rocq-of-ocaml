let[@rocq.wf] rec gcd left right =
  if right = 0 then left else gcd right (left mod right)

let[@rocq.wf] rec find_or default predicate values =
  match values with
  | [] -> default
  | value :: values ->
      if predicate value then value else find_or default predicate values
