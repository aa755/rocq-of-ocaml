let[@rocq.wf] rec countdown value =
  if value = 0 then assert false else countdown (value - 1)
