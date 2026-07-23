module type Input = sig
  val token : int
end

module Make (X : Input) = struct
  let identity x = x
  let pair x y = (X.token, x, y)
end
