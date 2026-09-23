let rec single (values : int list) =
  match values with
  | [] -> fun (result : int) -> result
  | _ :: tail -> fun (result : int) -> single tail result

let rec left (values : int list) =
  match values with
  | [] -> fun (result : int) -> result
  | _ :: tail -> fun (result : int) -> right tail result

and right (values : int list) =
  match values with
  | [] -> fun (result : int) -> result
  | _ :: tail -> fun (result : int) -> left tail result
