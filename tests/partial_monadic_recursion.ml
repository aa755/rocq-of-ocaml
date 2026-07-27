module type MONAD = sig
  type 'a t

  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
end

module Make (M : MONAD) = struct
  let rec count_down value =
    if value <= 0 then M.return 0
    else
      M.bind (M.return (value - 1)) (fun value -> count_down value)
end
