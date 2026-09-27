(* Compare the extracted executable parser with native Zarith on deterministic
   literal samples.  The extraction driver is created by check-zarith-parser.sh. *)
module NativeZ = Z
module M = Model_parser

let flag value = if value then M.True else M.False

let model_ascii character =
  let code = Char.code character in
  M.Ascii
    ( flag (code land 1 <> 0)
    , flag (code land 2 <> 0)
    , flag (code land 4 <> 0)
    , flag (code land 8 <> 0)
    , flag (code land 16 <> 0)
    , flag (code land 32 <> 0)
    , flag (code land 64 <> 0)
    , flag (code land 128 <> 0) )

let model_string value =
  let rec loop index =
    if index = String.length value then M.EmptyString
    else M.String (model_ascii value.[index], loop (index + 1))
  in
  loop 0

let rec positive = function
  | M.XH -> NativeZ.one
  | M.XO p -> NativeZ.mul (NativeZ.of_int 2) (positive p)
  | M.XI p -> NativeZ.succ (NativeZ.mul (NativeZ.of_int 2) (positive p))

let integer = function
  | M.Z0 -> NativeZ.zero
  | M.Zpos p -> positive p
  | M.Zneg p -> NativeZ.neg (positive p)

let model value =
  match M.of_string_opt (model_string value) with
  | M.Some parsed -> Some (integer parsed)
  | M.None -> None

let native value =
  try Some (NativeZ.of_string value) with Invalid_argument _ -> None

let checked = ref 0
let mismatches = ref 0

let check value =
  incr checked ;
  let expected = native value in
  let actual = model value in
  if expected <> actual then (
    incr mismatches ;
    if !mismatches <= 20 then
      Printf.printf "%S: native=%s model=%s\n" value
        (match expected with None -> "None" | Some n -> NativeZ.to_string n)
        (match actual with None -> "None" | Some n -> NativeZ.to_string n))

let alphabet = "0123456789abcdefABCDEFxXoObB_+- \t\r\n"

let rec exhaustive prefix remaining =
  check prefix ;
  if remaining > 0 then
    String.iter
      (fun character -> exhaustive (prefix ^ String.make 1 character) (remaining - 1))
      alphabet

let () =
  List.iter check
    [ "-+0xF"
    ; "0xF__F"
    ; "0o7_7"
    ; "0b1_0"
    ; "0x_F"
    ; "0o8"
    ; "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"
    ; "115792089237316195423570985008687907852837564279074904382605163141518161494337" ] ;
  exhaustive "" 3 ;
  let state = Random.State.make [| 0x5A17; 0xC0DE |] in
  for _ = 1 to 10000 do
    let length = Random.State.int state 25 in
    let value =
      String.init length (fun _ -> alphabet.[Random.State.int state (String.length alphabet)])
    in
    check value
  done ;
  Printf.printf "checked=%d mismatches=%d\n" !checked !mismatches ;
  if !mismatches > 0 then exit 1
