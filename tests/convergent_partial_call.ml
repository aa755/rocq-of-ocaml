module type RUNTIME = sig
  type 'a t

  val _return : 'a -> 'a t
  val op_letdollar : 'a t -> ('a -> 'b t) -> 'b t

  module Seq : sig
    val mapM : f:('a -> 'b t) -> 'a list -> 'b list t
  end
end

module Use (M : RUNTIME) = struct
  let collect values =
    M.Seq.mapM ~f:(fun value -> M._return (value + 1)) values
end
