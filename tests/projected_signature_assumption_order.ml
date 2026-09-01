module Make (P : sig
  val enabled : bool
end) = struct
  module Memory : sig
    val empty : int -> int
  end = struct
    let empty x =
      let () = if P.enabled then () else assert false in
      Option.get (Some x)
  end

  let initial x = Memory.empty x
end

module Built = Make (struct
  let enabled = true
end)

let initial = Built.initial
