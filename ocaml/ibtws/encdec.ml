open Pervasives;;
open Printf;;
open Char;;

let decode_string (ic: in_channel) : string =
  let n = 10000 in
  let s = String.make n (char_of_int 0) in
  let i = ref 0 in
  let c = ref (input_char ic) in
    while !i < n && !c != (char_of_int 0) do
      s.[!i] <- !c;
      c := (input_char ic);
      i := !i + 1;
    done;
    String.sub s 0 !i
;;

let decode_int (ic: in_channel) : int =
  let s = decode_string ic in
    int_of_string s
;;

let decode_float (ic: in_channel) : float =
  let s = decode_string ic in
    float_of_string s
;;


let int_max = max_int;;

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
    int_of_string s
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

let encode_float (f: float) (oc: out_channel) : unit =
  encode_string (sprintf "%.10f" f) oc
;;

let encode_bool (b: bool) (oc: out_channel) : unit =
  if b then 
    encode_int 1 oc
  else
    encode_int 0 oc
;;
