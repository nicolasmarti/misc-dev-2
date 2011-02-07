open Pervasives;;
open Printf;;
open Char;;

let decode_int (ic: in_channel) : int =
  let n = 100 in
  let s = String.make n (char_of_int 0) in
  let i = ref 0 in    
    (*printf "reading..."; flush stdout;*)
  let c = ref (input_char ic) in
    (*printf "read init = %c(%d)\n" !c (int_of_char !c); flush stdout;*)
    while !i < n && !c != (char_of_int 0) do
      (*printf "read: %c(%d)\n" !c (int_of_char !c); flush stdout;*)
      s.[!i] <- !c;
      (*printf "reading..."; flush stdout;*)
      c := (input_char ic);
      i := !i + 1;
    done;
    s.[!i] <- !c;
    (*printf "s:= '%s'\n" s;*)
    int_of_string (String.sub s 0 !i)
;;

let decode_float (ic: in_channel) : float =
  let n = 100 in
  let s = String.make n (char_of_int 0) in
  let i = ref 0 in    
    (*printf "reading..."; flush stdout;*)
  let c = ref (input_char ic) in
    (*printf "read init = %c(%d)\n" !c (int_of_char !c); flush stdout;*)
    while !i < n && !c != (char_of_int 0) do
      (*printf "read: %c(%d)\n" !c (int_of_char !c); flush stdout;*)
      s.[!i] <- !c;
      (*printf "reading..."; flush stdout;*)
      c := (input_char ic);
      i := !i + 1;
    done;
    s.[!i] <- !c;
    (*printf "s:= '%s'\n" s;*)
    float_of_string (String.sub s 0 !i)
;;

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


let encode_string (s: string) (oc: out_channel) : unit =
  String.iter (fun c -> output_char oc c) s;
  output_char oc (chr 0)
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
