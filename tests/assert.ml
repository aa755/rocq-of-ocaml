let checked_identity x =
  assert (x = x);
  x

let unreachable () : int = assert false
