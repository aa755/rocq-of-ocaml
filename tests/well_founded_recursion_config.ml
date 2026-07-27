module Arithmetic = struct
  let rec gcd left right =
    if right = 0 then left else gcd right (left mod right)
end
