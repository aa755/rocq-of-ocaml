module Wrapper (X : sig val initial : int end) = struct
  module Base = Project.Provider.Outer (X)
  include Base

  module Run (C : sig val enabled : bool end) = struct
    include Base.Run (C)
    let call flag = pair flag
  end
end
