module Run (S : Provider.STEP) = struct
  let rec run n = if n > 0 then run (S.step n) else n
end

module Forward (S : Provider.STEP) = struct
  module R = Run (S)
  let run n = R.run n
end

module Concrete = Forward (Provider.Reset)
let result = Concrete.run 12
