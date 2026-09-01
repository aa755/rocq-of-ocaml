let unavailable : int = assert false

let use_unavailable x = x + unavailable

let callbacks = [use_unavailable]
