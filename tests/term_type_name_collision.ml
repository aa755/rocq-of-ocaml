let identity (value : 'value) : 'value = value

let fold (combine : 'acc -> 'item -> 'acc) (acc : 'acc)
    (item : 'item) : 'acc =
  combine acc item
