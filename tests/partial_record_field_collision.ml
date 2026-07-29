type ('source, 'focus) lens = {
  get : 'source -> 'focus;
  set : 'focus -> 'source -> 'source;
}

let option_get = Option.get

let with_default (default : 'a) : ('a option, 'a) lens =
  {
    get = (function None -> default | Some value -> value);
    set = (fun value _ -> Some value);
  }
