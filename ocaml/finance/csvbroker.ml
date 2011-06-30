open Planck;;

(* Stream of chars with buffering and memoization *)
module Stream = struct

  (* The configuration of the stream *)    
  module Base = struct

    (* Stream elements *)
    type elem = char (* It is a char stream *)
    let show_elem = Printf.sprintf "%C" (* How to pretty print the element *)
    let equal_elem (x : char) y = x = y

    (* Stream attributes *)
    type attr = Sbuffer.buf (* Stream elements carry internal buffers *)
    let default_attr = Sbuffer.default_buf

    (* Stream positions *)
    module Pos = Position.File (* Type of the element position *)
    let position_of_attr attr = Sbuffer.position_of_buf attr (* How to obtain the position from attr *)
  end

  module Str = Stream.Make(Base) (* Build the stream *)
  include Str

  (* Extend Str with buffering *)
  include Sbuffer.Extend(struct
    include Str
    let create_attr buf = buf (* How to create an attribute from a buffer *)
    let buf st = attr st (* How to obtain the buffer of a stream *)
  end)

end

module Parser = struct

  module Base = Pbase.Make(Stream) (* Base parser *)
  include Base

  include Pbuffer.Extend(Stream)(Base) (* Extend Base with parser operators for buffered streams *)
end    

open Parser (* open Parser namespace *)

let blank = ignore (one_of [' '; '\t'; '\n'; '\r'])

let parse_elt st = begin
  
  matched (?+ (tokenp (function | '(' | ')' | '"' | ';' | ' ' | ',' | '\t' | '\n' | '\r' | '\'' -> false | _ -> true) <?> "var")) >>= fun s2 -> 
  return s2
    
end st

let parse_line st = begin
  (list_with_sep 
     ~sep:(token ',') 
     parse_elt
  ) >>= fun [bdate; bopen; bhigh; blow; bclose; bvolume; badjustclose] ->
  return (float_of_string badjustclose)

end st  

let parse_lines st = begin
  (list_with_sep 
     ~sep:(?+ blank) 
     parse_line
  )
end st  

let parse_csv csv =
  let stream = Stream.from_string ~filename:"stdin" csv in
  match parse_lines stream with
    | Result.Ok (res, _) -> (
      res
    )
    | Result.Error (pos, s) ->
      Format.eprintf "%s\n%a: syntax error: %s@." csv Position.File.format pos s;      
      raise Pervasives.Exit
;;

open Finance_intf;;

module CSVBroker =
struct

  type status = RUNNING
		| STOPPED

  type t = {
    close: float list;
    mutable index: int;
    mutable st: status;
  };;

  type data = float list;;

  type info = string;;

  let init info = {close = List.rev (parse_csv info);
		   index = 0;
		   st = STOPPED;
		  };;

  let start t = t.st <- RUNNING;;
  let stop t = t.st <- STOPPED; t.index <- 0;;
  let getstatus t = t.st;;
  
  let rec take l n =
    match n with
      | 0 -> []
      | n -> 
	match l with
	  | [] -> []
	  | hd::tl -> hd::(take tl (n-1))
  ;;

  let getdata t = 
    if t.index >= List.length t.close then
      (t.st <- STOPPED; t.close)
    else
      let i = t.index in t.index <- t.index + 1; take t.close i
  ;;
  
  type order = int;;

  type orderId = int * int;;

  type orderRes = Filled
		  | Cancelled
		  | Pending
  ;;

  let proceedOrder t o = (t.index, o);;
  let orderStatus t oid = Filled;;
  let cancelOrder t oid = ();;
  let closeOrder t (index, o) = (t.index, -o);;
  let orderValue t (index, o) = (List.nth t.close index) *. float o;;
  let orderPnL t (index, o) = (List.nth t.close t.index -. List.nth t.close index) *. float o;;

end;;

