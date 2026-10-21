module Outer (X : sig val initial : int end) = struct
  module Run (C : sig val enabled : bool end) = struct
    let pair flag : int * string =
      let number = if flag then assert false else X.initial in
      let text = if C.enabled then assert false else "ok" in
      (number, text)
  end
end
