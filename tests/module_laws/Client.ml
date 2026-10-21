module Again = Consumer.Forward (Provider.Reset)
let run n = Again.run n
let from_local = Consumer.result

module Direct = Consumer.Run (Provider.Reset)
let direct n = Direct.run n

module Local = struct
  let step = Provider.Reset.step
end

module LocalDirect = Consumer.Run (Local)
let local_direct n = LocalDirect.run n
