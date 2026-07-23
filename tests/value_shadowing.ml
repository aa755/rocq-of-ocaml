let rec sum values =
  match values with
  | [] -> 0
  | value :: values -> value + sum values

let sum initial values = initial + sum values

let example = sum 10 [ 1; 2 ]
