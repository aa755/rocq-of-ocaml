module Outer (X : sig val initial : int end) = struct
  module Run (C : sig val enabled : bool end) = struct
    let pair flag : int * string =
      let number = if flag then assert false else X.initial in
      let text = if C.enabled then assert false else "ok" in
      (number, text)
  end
end

module Wrapper (X : sig val initial : int end) = struct
  module Base = Outer (X)
  include Base

  module Run (C : sig val enabled : bool end) = struct
    include Base.Run (C)
    let call flag = pair flag
  end
end
