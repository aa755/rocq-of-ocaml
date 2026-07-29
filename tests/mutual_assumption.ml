type even =
  | Zero
  | EvenSucc of odd

and odd = OddSucc of even

let rec even_to_int = function
  | Zero -> 0
  | EvenSucc value -> odd_to_int value

and odd_to_int = function
  | OddSucc value ->
      assert (even_to_int value >= 0);
      1
