module type S = sig
  type ('a, 'error) t

  val return : 'a -> ('a, 'error) t
end

module Make (M : S) = struct
  include M

  module Option = struct
    type 'a t = 'a option

    let iterM (value : 'a option)
        ~(f : 'a -> (unit, 'error) M.t) : (unit, 'error) M.t =
      match value with
      | Some value -> f value
      | None -> M.return ()
  end
end

include Stdlib.Result

include Make (struct
  type nonrec ('a, 'error) t = ('a, 'error) t

  let return value = Ok value
end)
