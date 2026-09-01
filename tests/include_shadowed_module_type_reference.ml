module Result (T : sig
  type error
end) = struct
  type error = T.error

  let id (value : error) = value
end

module Build (T : sig
  type error
end) = struct
  module Result : sig
    type error

    val id : error -> error
  end = struct
    include Result (T)
  end

  let fail (error : Result.error) value = (error, value)
end

module M = struct
  module Base = Build (struct
    type error = int
  end)

  include Base

  module Result = struct
    let marker = true
  end
end
