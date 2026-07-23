module type Ordered = sig
  type t

  val compare : t -> t -> int
end

module type Also_ordered = sig
  type t

  val compare : t -> t -> int
end

module type Ordered_alias = Ordered

module type Same_shape_but_different_type = sig
  type t

  val compare : t -> int -> int
end

module Make
    (X : sig
       type t

       val compare : t -> t -> int
     end) =
struct
  let compare = X.compare
end

module Int_ordered : Ordered = struct
  type t = int

  let compare (x : int) y = x - y
end

module Int_comparison = Make (Int_ordered)
