exception Failure_case

let failed_int () : int =
  failwith "impossible"

let invalid_string () : string =
  invalid_arg "invalid"

let raised_bool () : bool =
  raise Failure_case

let missing_implementation () : int =
  failwith "todo 17"

let failed_poly () : 'a =
  failwith "impossible polymorphic result"

let failed_poly_int () : int =
  failed_poly ()

module Outer (X : sig
  type t

  val value : t
end) =
struct
  module Inner (Y : sig
    val valid : bool
  end) =
  struct
    let checked () : X.t =
      assert Y.valid ;
      X.value
  end
end

module Provider (X : sig end) = struct
  module List = struct
    let hd values =
      List.hd values
  end
end

module Consumer (X : sig end) = struct
  module Instantiation = Provider (X)
  module List = Instantiation.List

  let head values =
    List.hd values
end
