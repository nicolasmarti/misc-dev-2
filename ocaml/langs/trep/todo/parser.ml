open Spotlib.Spot
open Planck
open Pprinter;;
open Printer;;
open Printf;;


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

open Def

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

	 | "Array" -> error "reserved keyword: array"
	 | "Unit" -> error "reserved keyword: unit"
	 | "Int" -> error "reserved keyword: int"
	 | "Double" -> error "reserved keyword: double"
	 | "Float" -> error "reserved keyword: Float"
	 | "Bool" -> error "reserved keyword: Bool"
	 | "Mutable" -> error "reserved keyword: Mutable"

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
    return AVar  
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


let rec parse_kind st = begin
  try_ (
    surrounded (?* blank) (?* blank) parse_basekind >>= fun lhs ->
    surrounded (?* blank) (?* blank) (parse_string "->") >>= fun _ ->
    surrounded (?* blank) (?* blank) parse_kind >>= fun rhs ->
      return (KImpl (lhs, rhs))
  )
  <|> try_ parse_basekind
end st
    
and parse_basekind st = begin
  try_ (surrounded (?* blank) (?* blank) (token '*' >>= fun _ -> return KStar))
  <|> try_ (surrounded (surrounded (?* blank) (?* blank) (token '(')) (surrounded (?* blank) (?* blank) (token ')')) parse_kind)
end st

let constant_int st = begin
  (* [0-9]+ *)
  (matched (?+ (tokenp (function '0'..'9' -> true | _ -> false) <?> "decimal")) >>= fun s -> 
   return (int_of_string s))
end st


let rec parse_mltype st = begin
  try_ (
    surrounded (?* blank) (?* blank) parse_appmltype >>= fun lhs ->
    surrounded (?* blank) (?* blank) (parse_string "->") >>= fun _ ->
    surrounded (?* blank) (?* blank) parse_mltype >>= fun rhs ->  
      return (TyApp (TyImpl, [lhs; rhs]))
  )
  <|> try_ (surrounded (?* blank) (?* blank) parse_appmltype)
end st

and parse_appmltype st = begin
  list_with_sep ~sep:(?+ blank)
    (
      try_ parse_basemltype
      <|> try_ (surrounded (surrounded (?* blank) (?* blank) (token '(')) (surrounded (?* blank) (?* blank) (token ')')) parse_mltype)
    ) >>= fun l ->
      match l with
	| [] -> raise (Failure "this case should never happen")
	| hd::[] -> return hd
	| hd::tl -> return (TyApp (hd, tl))

end st

and parse_basemltype st = begin
  try_ (parse_name >>= fun s -> return (TyVar s))
end st

	  


let rec parse_term (leftmost: Pos.t) : term Parser.t =
  ?* blank >>= fun () ->
    parse_leftmost leftmost (
      withPos (with_type (parse_appterm leftmost)) >>= fun (te, startp, endp) ->
	return (SrcInfo (te, startp, endp))
    )

and with_type (p: term Parser.t) : term Parser.t =
  p >>= fun res ->
  option
    (
      ?* blank >>= fun _ ->
      parse_string "::" >>= fun _ ->
      ?* blank >>= fun _ ->
	parse_mltype
    ) >>= fun ty ->
      match ty with
	| None -> return res
	| Some ty -> return (Annotated (res, ty))
	  
and parse_appterm (leftmost: Str.Pos.t) : term Parser.t =
  list_with_sep ~sep:(?+ blank <|> eos) 
    (
      (*
	try_ (withPos (parse_baseterm leftmost) >>= fun (te, startp, endp) ->
	return (SrcInfo (te, startp, endp))
	)
      *)
      try_ (parse_baseterm leftmost)
      <|> try_ (surrounded (token '(' >>= fun _ -> ?* blank >>= fun () -> return ()) (?* blank >>= fun () -> token ')') (parse_term Pos.none))
    )
  >>= fun l -> 
    match l with
      | [] -> raise (Failure "this case should never happen")
      | hd::[] -> return hd
      | hd::tl -> return (App (hd, tl))

and parse_baseterm (leftmost: Str.Pos.t) : term Parser.t =
  parse_leftmost leftmost (
    withPos(
     try_ (parse_letbind leftmost)
     <|> try_ (parse_case leftmost)
     <|> try_ (parse_ifte leftmost)
     <|> try_ (parse_lambda leftmost)
     <|> try_ (parse_alias leftmost)
     <|> try_ parse_var 
     <|> try_ parse_avar
    ) 
  ) >>= fun (te, startp, endp) ->
    return (SrcInfo (te, startp, endp))
 
and parse_alias (leftmost: Pos.t) : term Parser.t =  
  parse_name >>= fun alias ->
  token '@'  >>= fun _ -> 
  parse_term leftmost >>= fun te ->
    return (Alias (alias, te))

and parse_letbind (leftmost: Pos.t) : term Parser.t =
  parse_string "let" >>= fun _ ->
  ?+ blank >>= fun _ ->

  option (
    parse_string "rec" >>= fun _ ->
    ?+ blank) >>= fun r ->

  list_with_sep ~sep:(surrounded (?* blank) (?* blank) (token ';')) 
    (
      parse_term leftmost >>= fun pattern ->
      surrounded (?* blank) (?* blank) (parse_string ":=") >>= fun _ ->
      parse_term leftmost >>= fun value ->	
	return (pattern, value)
    ) >>= fun bindings ->

  (surrounded (?+ blank) (?+ blank) (parse_string "in")) >>= fun _ ->

  parse_term leftmost >>= fun te ->
    return (Let ((match r with Some _ -> true | _ -> false), bindings, te))    

and parse_lambda (leftmost: Pos.t) : term Parser.t =
  parse_string "\\" >>= fun _ ->
  ?+ blank >>= fun _ ->

  list_with_sep ~sep:(?+ blank)
    (
      try_ (parse_basepattern leftmost) 
      <|> (surrounded (token '(' >>= fun _ -> ?* blank >>= fun () -> return ()) (?* blank >>= fun () -> token ')') (parse_pattern Pos.none))
    ) >>= fun patterns ->

  (surrounded (?* blank) (?* blank) (parse_string "->")) >>= fun _ ->

  parse_term leftmost >>= fun te ->
    return (Lambda (patterns, te))    

and parse_case (leftmost: Pos.t) : term Parser.t =
  parse_string "case" >>= fun _ ->
  ?+ blank >>= fun _ ->

  parse_term leftmost >>= fun te ->
  ?+ blank >>= fun _ ->

  parse_string "of" >>= fun _ ->
  ?+ blank >>= fun _ ->

  token '|' >>= fun _ ->
  ?+ blank >>= fun _ ->

  list_with_sep ~sep:(surrounded (?* blank) (?* blank) (token '|'))   
    (
      parse_equation leftmost
    ) >>= fun cases ->
      return (Case (te, cases))

and parse_equation (leftmost: Pos.t) : equation Parser.t =

  position >>= fun equation_pos ->

  parse_term leftmost >>= fun te ->
  ?+ blank >>= fun _ ->
    
  option (
    parse_string "with" >>= fun _ ->
    ?+ blank >>= fun _ ->

    list_with_sep ~sep:(surrounded (?* blank) (?* blank) (parse_string "with"))   
      (
	parse_term equation_pos >>= fun guard ->
	?+ blank >>= fun _ ->
	surrounded (?* blank) (?* blank) (parse_string ":=") >>= fun _ ->
	parse_term equation_pos >>= fun value ->	
	  return (guard, value)
      )
  ) >>= fun guarded ->
    match guarded with
      | Some gs -> return (Guarded (te, gs))
      | None ->
	  surrounded (?* blank) (?* blank) (parse_string ":=") >>= fun _ ->
	  parse_term equation_pos >>= fun value ->	
	    return (NotGuarded (te, value))

and parse_ifte (leftmost: Pos.t) : term Parser.t =	  
  parse_string "if" >>= fun _ ->
  ?+ blank >>= fun _ ->

  parse_term leftmost >>= fun b ->
  ?+ blank >>= fun _ ->

  parse_string "then" >>= fun _ ->
  ?+ blank >>= fun _ ->

  parse_term leftmost >>= fun c1 ->
  ?+ blank >>= fun _ ->

  parse_string "else" >>= fun _ ->
  ?+ blank >>= fun _ ->

  parse_term leftmost >>= fun c2 ->
  ?+ blank >>= fun _ ->
    return (Ifte (b, c1, c2))
;;

open Position

let test_term s = 
  Format.eprintf "input=%S@." s;
  let stream = Stream.from_string ~filename:"stdin" s in
  match (parse_term (Position.File.top "test")) stream with
  | Result.Ok (res, _) -> 
      printbox (token2box (term2token res) 400 2)
  | Result.Error (pos, s) ->
      Format.eprintf "%a: syntax error: %s@." Position.File.format pos s;
      raise Exit
;;

