let inspect left right =
  ( Iarray.length left,
    Iarray.fold_right ( + ) left 0,
    Iarray.exists2 ( = ) left right,
    Iarray.to_list (Iarray.of_list [ 1; 2; 3 ]) )
