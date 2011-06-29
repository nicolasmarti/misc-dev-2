open Pervasives;;
open Printf;;
open Char;;
open Int64;;

let decode_string (ic: in_channel) : string =
  if false then (
    let n = 100000 in
    let s = String.make n (char_of_int 0) in
    let i = ref 0 in
    let c = ref (input_char ic) in
    while !i < n && !c != (char_of_int 0) do
      s.[!i] <- !c;
      c := (input_char ic);
      i := !i + 1;
    done;
    String.sub s 0 !i
  ) else (
    let s = Buffer.create 1000 in
    let c = ref (input_char ic) in
    while !c != (char_of_int 0) do
      Buffer.add_char s !c;
      c := input_char ic
    done;
    Buffer.contents s
  )
;;

let decode_int (ic: in_channel) : int =
  let s = decode_string ic in
  try 
    int_of_string s
  with
    | _ -> raise (Failure (String.concat "" ["decode_int: "; s]))
;;

let decode_float (ic: in_channel) : float =
  let s = decode_string ic in
    float_of_string s
;;

let decode_int64 (ic: in_channel) : int64 =
  let s = decode_string ic in
    of_string s
;;

let decode_bool (ic: in_channel) : bool =
  let s = decode_string ic in
    match s with
      | "1" -> true
      | "0" -> false
      | _ -> raise (Failure "decode_bool")
;;

let int_max = Pervasives.max_int;;

let dbl_max = max_float;;

let decode_float_max (ic: in_channel) : float =
  let s = decode_string ic in
  if s = "" then 
    dbl_max
  else
    float_of_string s
;;

let decode_int_max (ic: in_channel) : int =
  let s = decode_string ic in
  if s = "" then 
    int_max
  else
    try
      int_of_string s
    with
      | _ -> raise (Failure (String.concat "" ["decode_int_max: "; s]))


;;


let encode_string (s: string) (oc: out_channel) : unit =
  String.iter (fun c -> output_char oc c) s;
  output_char oc (chr 0)
;;


let encode_int_max (i: int) (oc: out_channel) : unit =
  if i = int_max then
    encode_string "" oc 
  else
    encode_string (string_of_int i) oc 
;;


let encode_float_max (f: float) (oc: out_channel) : unit =
  if f = dbl_max then 
    encode_string "" oc
  else
    encode_string (sprintf "%.10f" f) oc
;;

let encode_int (i: int) (oc: out_channel) : unit =
  encode_string (string_of_int i) oc 
;;

let encode_int64 (i: int64) (oc: out_channel) : unit =
  encode_string (to_string i) oc 
;;

let encode_float (f: float) (oc: out_channel) : unit =
  encode_string (sprintf "%.10f" f) oc
;;

let encode_bool (b: bool) (oc: out_channel) : unit =
  if b then 
    encode_int 1 oc
  else
    encode_int 0 oc
;;
