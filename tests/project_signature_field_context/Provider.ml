module Make (Argument : sig
  val value : int
end) = struct
  let value = Argument.value
  let missing flag = if flag then value else assert false
end
