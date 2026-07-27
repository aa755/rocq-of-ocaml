let search bound =
  let rec loop value = if value < bound then loop (value + 1) else value in
  loop 0
