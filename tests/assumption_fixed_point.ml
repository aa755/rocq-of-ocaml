let leaf : int = assert false

let middle () = leaf

let root () =
  assert true;
  middle ()
