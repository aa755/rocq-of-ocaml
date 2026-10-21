module type STEP = sig
  val step : int -> int
end

module Reset : STEP = struct
  let step _ = 0
end

module Identity : STEP = struct
  let step n = n
end
