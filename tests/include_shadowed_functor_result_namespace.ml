module Make (Arg : sig
  val witness : unit
end) = struct
  let witness = Arg.witness

  module Option = struct
    type 'a t = 'a option

    let none = None
    let some value = Some value
    let inherited value default = match value with None -> default | Some x -> x
  end
end

module M = struct
  module Base = Make (struct
    let witness = ()
  end)

  include Base

  module Option = struct
    include Option

    let inherited value default =
      match value with None -> default | Some x -> x

    let local = some 1
  end
end
