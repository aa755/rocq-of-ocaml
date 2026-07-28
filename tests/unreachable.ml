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

let failed_function (_ : unit) : int =
  failwith "impossible function"

let failed_function_alias =
  failed_function

module Qualified = struct
  let failed_unit () : unit =
    assert false
end

let failed_qualified () : unit =
  Qualified.failed_unit ()

module Make_projected (X : sig
  val marker : unit
end) = struct
  let failed_unit () : unit =
    assert false
end

module Projected = Make_projected (struct
  let marker = ()
end)

let failed_projected () : unit =
  Projected.failed_unit ()

module Abstract_failure (Value : sig
    type t
  end) =
struct
  type t = Value.t

  let failed () : Value.t =
    assert false

  let observes_failure (_ : t) =
    let _ = failed () in
    true
end

module Observed_failure = Abstract_failure (struct
  type t = int
end)

module Included_failure = struct
  include Observed_failure
end

let failed_included () : Included_failure.t =
  Included_failure.failed ()

module Shadowed_pattern = struct
  let hd values =
    List.hd values

  let first_or_zero = function
    | hd :: _ -> hd
    | [] -> 0
end

module Scoped_value (X : sig
  val value : [> `Number of int]
end) =
struct
  let number =
    match X.value with
    | `Number value -> value

  module Nested = struct
    let copied_number = number
  end
end

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
