open Spotlib.Spot
open Planck
open Pprinter;;
open Printf;;

open Trep;;

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

open Op_prec (* open Op_prec, functions for operator precedences *)

(* parsing a term
   - leftmost: correspond to the leftmost position possible for a term
               it correspond to the begining position of the term (== following the declaration header)
               
               
*)

(* module Pos = Str.Pos *)
module Pos = Position.File
;;

let withPos (p: 'a Parser.t) st = begin
  position >>= fun start_pos -> 
  p >>= fun res ->
  position >>= fun end_pos ->  
    return (res, start_pos, end_pos)
end st

let parse_name st = begin
    (matched (?+ (tokenp (function 'a'..'z' -> true | 'A'..'Z' -> true | _ -> false) <?> "var")) >>= fun s -> 
       match s with
	 | "let" -> error "reserved keyword: let"
	 | "in" -> error "reserved keyword: in"
	 | "case" -> error "reserved keyword: case"
	 | "of" -> error "reserved keyword: of"
	 | "where" -> error "reserved keyword: where"
	 | "with" -> error "reserved keyword: with"
	 | "if" -> error "reserved keyword: if"
	 | "then" -> error "reserved keyword: then"
	 | "else" -> error "reserved keyword: else"

	 | "Type" -> error "reserved keyword: Type"

	 | _ -> return s
    )    
end st

let parse_var st = begin
    (parse_name >>= fun s -> 
       return (Var (None, s))
    )
end st

let parse_avar st = begin
  token '_'  >>= fun _ -> 
    return (AVar None) 
end st

let blank = ignore (one_of [' '; '\t'; '\n'; '\r'])

let rec string2listchar (s: string) : char list =
  if String.length s = 0 then []
  else
    (String.get s 0)::(string2listchar (String.sub s 1 (String.length s - 1)))

let parse_string (s: string) : unit Parser.t =
  tokens (string2listchar s)

let parse_leftmost (leftmost: Pos.t) (p : 'a Parser.t) : 'a Parser.t =
  position >>= fun curr_pos ->
    if curr_pos.Pos.column < leftmost.Pos.column then
      error "Lefter than leftmost"
    else
      p

let constant_int st = begin
  (* [0-9]+ *)
  (matched (?+ (tokenp (function '0'..'9' -> true | _ -> false) <?> "decimal")) >>= fun s -> 
   return (int_of_string s))
end st

let rec parse_term (leftmost: Pos.t) : term Parser.t =
  ?* blank >>= fun () ->
    parse_leftmost leftmost (
      withPos (with_type (parse_appterm leftmost)) >>= fun (te, startp, endp) ->
	return (SrcInfo (te, (startp, endp)))
    )

and with_type (p: term Parser.t) : term Parser.t =
  p >>= fun res ->
  option
    (
      ?* blank >>= fun _ ->
      parse_string "::" >>= fun _ ->
      ?* blank >>= fun _ ->
	p
    ) >>= fun ty ->
      match ty with
	| None -> return res
	| Some ty -> return (TyAnnotation (res, (Annotated ty)))
	  
and parse_appterm (leftmost: Str.Pos.t) : term Parser.t =
  list_with_sep ~sep:(?+ blank <|> eos) 
    (
      try_ (parse_baseterm leftmost >>= fun res -> return (res, Explicit))
      <|> try_ (surrounded (token '(' >>= fun _ -> ?* blank >>= fun () -> return ()) (?* blank >>= fun () -> token ')') (parse_term Pos.none >>= fun res -> return (res, Explicit)))
      <|> try_ (surrounded (token '{' >>= fun _ -> ?* blank >>= fun () -> return ()) (?* blank >>= fun () -> token '}') (parse_term Pos.none >>= fun res -> return (res, Hidden)))
      <|> try_ (surrounded (token '[' >>= fun _ -> ?* blank >>= fun () -> return ()) (?* blank >>= fun () -> token ']') (parse_term Pos.none >>= fun res -> return (res, Implicit))) 
    )
  >>= fun l -> 
    match l with
      | [] -> raise (Failure "this case should never happen")
      | hd::[] -> return (fst hd)
      | hd::tl -> return (App (fst hd, tl))

and parse_baseterm (leftmost: Str.Pos.t) : term Parser.t =
  parse_leftmost leftmost (
    withPos((*
     try_ (parse_letbind leftmost)
     <|> try_ (parse_case leftmost)
     <|> try_ (parse_ifte leftmost)
     <|> try_ (parse_lambda leftmost)
     <|> try_ (parse_alias leftmost)*)
     try_ parse_Type
     <|> try_ parse_var 
     <|> try_ parse_avar
    ) 
  ) >>= fun (te, startp, endp) ->
    return (SrcInfo (te, (startp, endp)))
 
and parse_Type : term Parser.t =  
  parse_string "Type" >>= fun _ -> 
  return (Type None)
;;
