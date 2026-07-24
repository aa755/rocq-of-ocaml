type state = {
  remaining : int;
}

let rec run current =
  if current.remaining = 0 then
    current
  else
    run {remaining = current.remaining - 1}
