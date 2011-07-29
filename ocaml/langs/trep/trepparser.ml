open Spotlib.Spot
open Planck
open Pprinter;;
open Printf;;

open Def;;
open Trepprinter;;

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

	 | "inductive" -> error "reserved keyword: inductive"

	 | _ -> return s
    )    
end st

let parse_var st = begin
    try_ parse_name
end st

let parse_avar st = begin
  token '_'  >>= fun _ -> 
    return () 
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
    if curr_pos.Pos.column < leftmost.Pos.column then (
      printf "Lefter than leftmost\n";
      error "Lefter than leftmost"
    )
    else
      p

let constant_int st = begin
  (* [0-9]+ *)
  (matched (?+ (tokenp (function '0'..'9' -> true | _ -> false) <?> "decimal")) >>= fun s -> 
   return (int_of_string s))
end st

(*fold : ('a -> 'b -> 'c -> 'c) -> ('a, 'b) t -> 'c -> 'c*)

let infix_pattern st = begin
  Hashtbl.fold (fun symb op acc ->
    match op.kind with
      | `Infix _ -> (
	try_ (parse_string symb >>= fun () ->
	      return (Op_prec.infix symb (fun left right -> 
		PApp (PCste (Symbol (symb, op), AVar), [(left, Explicit); (right, Explicit)], AVar)
	      )
	      )
	) <|> acc
      )
      | _ -> acc
  ) Op_prec.tbl (error "Not a infix")
end st

let binop_pattern st = begin
  Hashtbl.fold (fun symb op acc ->
    try_ (surrounded 
	 (token '(' >>= fun _ -> ?* blank >>= fun () -> return ()) 
	 (?* blank >>= fun () -> token ')') 
	 (parse_string symb) >>= fun () -> return (PCste (Symbol (symb, op), AVar))
    ) <|> acc
  ) Op_prec.tbl (error "Not a binop")
end st

let infix_term st = begin
  Hashtbl.fold (fun symb op acc ->
    match op.kind with
      | `Infix _ -> (
	try_ (parse_string symb >>= fun () ->
	      return (Op_prec.infix symb (fun left right -> 
		App (Cste (Symbol (symb, op)), [(left, Explicit); (right, Explicit)])
	      )
	      )
	) <|> acc
      )
      | _ -> acc
  ) Op_prec.tbl (error "Not a infix")
end st

let binop_term st = begin
  Hashtbl.fold (fun symb op acc ->
    try_ (surrounded 
	 (token '(' >>= fun _ -> ?* blank >>= fun () -> return ()) 
	 (?* blank >>= fun () -> token ')') 
	 (parse_string symb) >>= fun () -> return (Cste (Symbol (symb, op)))
    ) <|> acc
  ) Op_prec.tbl (error "Not a binop")
end st

let combine_leftrec (non_leftrec : 'a Parser.t) (leftrec : 'a -> 'a Parser.t) =
  
  non_leftrec >>= fun left ->
  
  let rec leftrecs left =
    try_ (leftrec left >>= fun left' -> leftrecs left')
    <|> return left
  in
  leftrecs left

let parse_Type : unit Parser.t =  
  parse_string "Type" >>= fun _ -> 
  return ()
;;

let rec parse_pattern (leftmost: Pos.t) : pattern Parser.t =
  try_ (expr_pattern leftmost >>= fun x -> return (build x))
  <|> try_ (
    ?* blank >>= fun () ->
    parse_leftmost leftmost (
      (parse_apppattern leftmost) >>= fun te ->
      return te
    )
  )
and expr_pattern (leftmost: Pos.t) st = begin

  combine_leftrec (expr_pattern_non_leftrec leftmost) (expr_pattern_leftrec leftmost)

end st

and expr_pattern_non_leftrec (leftmost: Pos.t) st = begin (* constant, parened and unary minus *)  

  (* Skip spaces *)
  ?* blank >>= fun () -> 

  try_ (parse_apppattern leftmost >>= fun sv -> return (Op_prec.terminal sv))

  <|> try_ (token '(' >>= fun () ->
       ?* blank >>= fun () ->
       expr_pattern leftmost  >>= fun e ->
       ?* blank >>= fun () ->
       token ')' <?> "missing closing paren" >>= fun () ->
       return (Op_prec.parened (fun s -> s) e))
      
(*

  TODO: fold for prefix
  (* Unary minus *)      
  <|> (token '-' >>= fun () ->
       ?* blank >>= fun () ->
       expr >>= fun e ->
       return (prefix "~" (fun (s,v) -> Printf.sprintf "~ %s" s, -v) e))
*)

end st

and expr_pattern_leftrec (leftmost: Pos.t) e_left st = begin (* binop expr *)

  ?* blank >>= fun () ->

  (infix_pattern >>= fun binop ->
   ?* blank >>= fun () ->
   expr_pattern leftmost >>= fun e_right ->
   return (binop e_left e_right))

end st

and parse_apppattern (leftmost: Str.Pos.t) : pattern Parser.t =
  list_with_sep ~sep:(?+ blank <|> eos) 
    (
      try_ (parse_basepattern leftmost >>= fun res -> return (res, Explicit))
      <|> try_ (surrounded (token '(' >>= fun _ -> ?* blank >>= fun () -> return ()) (?* blank >>= fun () -> token ')') (parse_pattern Pos.none >>= fun res -> return (res, Explicit)))
      <|> try_ (surrounded (token '{' >>= fun _ -> ?* blank >>= fun () -> return ()) (?* blank >>= fun () -> token '}') (parse_pattern Pos.none >>= fun res -> return (res, Hidden)))
      <|> try_ (surrounded (token '[' >>= fun _ -> ?* blank >>= fun () -> return ()) (?* blank >>= fun () -> token ']') (parse_pattern Pos.none >>= fun res -> return (res, Implicit))) 
    )
  >>= fun l -> 
    match l with
      | [] -> raise (Failure "this case should never happen")
      | hd::[] -> return (fst hd)
      | hd::tl -> return (PApp (fst hd, tl, AVar))

and parse_basepattern (leftmost: Str.Pos.t) : pattern Parser.t =
  parse_leftmost leftmost (
    try_ binop_pattern
    <|> try_ (parse_alias leftmost)
    <|> try_ (parse_Type >>= fun () -> return (PType None))
    <|> try_ (parse_var >>= fun s -> return (PVar (s, AVar)))
    <|> try_ (parse_avar >>= fun () -> return (PAVar AVar))
    <|> try_ (surrounded (token '(' >>= fun _ -> ?* blank >>= fun () -> return ()) (?* blank >>= fun () -> token ')') (parse_pattern Pos.none >>= fun res -> return res))
  ) >>= fun te ->
  return te

and parse_alias (leftmost: Pos.t) : pattern Parser.t =  
  parse_name >>= fun alias ->
  token '@'  >>= fun _ -> 
  parse_basepattern leftmost >>= fun te ->
    return (PAlias (alias, te, AVar))

;;

let rec parse_term (leftmost: Pos.t) : term Parser.t =
  try_ (parse_impl leftmost)
  <|> try_ (expr_term leftmost >>= fun x -> return (build x))
  <|> try_ (
    ?* blank >>= fun () ->
    parse_leftmost leftmost (
      withPos (with_type (parse_appterm leftmost)) >>= fun (te, startp, endp) ->
      return (SrcInfo (te, (startp, endp)))
    )
  )

(* Eta expansions with [st] are required, unfortunatelly *)
and expr_term (leftmost: Pos.t) st = begin

  combine_leftrec (expr_term_non_leftrec leftmost) (expr_term_leftrec leftmost)

end st

and expr_term_non_leftrec (leftmost: Pos.t) st = begin (* constant, parened and unary minus *)  

  (* Skip spaces *)
  ?* blank >>= fun () -> 

  try_ (parse_appterm leftmost >>= fun sv -> return (Op_prec.terminal sv))

  <|> try_ (token '(' >>= fun () ->
       ?* blank >>= fun () ->
       expr_term leftmost  >>= fun e ->
       ?* blank >>= fun () ->
       token ')' <?> "missing closing paren" >>= fun () ->
       return (Op_prec.parened (fun s -> s) e))
      
end st

and parse_impl (leftmost: Pos.t) : term Parser.t =
  parse_quantifier_impl leftmost >>= fun quantifier ->
  
  (surrounded (?* blank) (?* blank) (parse_string "->")) >>= fun _ ->
  
  parse_term leftmost >>= fun te ->
    return (Impl (quantifier, te))    


and expr_term_leftrec (leftmost: Pos.t) e_left st = begin (* binop expr *)

  ?* blank >>= fun () ->

  (infix_term >>= fun binop ->
   ?* blank >>= fun () ->
   expr_term leftmost >>= fun e_right ->
   return (binop e_left e_right))

end st


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
	  
and parse_appterm (leftmost: Str.Pos.t) st = begin
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
end st

and parse_baseterm (leftmost: Str.Pos.t) : term Parser.t =
  parse_leftmost leftmost (
    withPos(
     try_ (parse_letbind leftmost)
     <|> try_ (parse_case leftmost)
     <|> try_ (parse_ifte leftmost)
     <|> try_ (parse_lambda leftmost)
     <|> try_ binop_term
     <|> try_ (parse_Type >>= fun () -> return (Type None))
     <|> try_ (parse_var >>= fun s -> return (Var (Left s)))
     <|> try_ (parse_avar >>= fun () -> return AVar)
     <|> try_ (surrounded (token '(' >>= fun _ -> ?* blank >>= fun () -> return ()) (?* blank >>= fun () -> token ')') (parse_term Pos.none >>= fun res -> return res))
    ) 
  ) >>= fun (te, startp, endp) ->
    return (SrcInfo (te, (startp, endp)))

and parse_letbind (leftmost: Pos.t) : term Parser.t =
  parse_string "let" >>= fun _ ->
  ?+ blank >>= fun _ ->

  option (
    parse_string "rec" >>= fun _ ->
    ?+ blank) >>= fun r ->

  list_with_sep ~sep:(surrounded (?* blank) (?* blank) (token ';')) 
    (
      parse_pattern leftmost >>= fun pattern ->
      surrounded (?* blank) (?* blank) (parse_string ":=") >>= fun _ ->
      parse_term leftmost >>= fun value ->	
	return (pattern, value)
    ) >>= fun bindings ->

  (surrounded (?+ blank) (?+ blank) (parse_string "in")) >>= fun _ ->

  parse_term leftmost >>= fun te ->
    return (Let ((match r with Some _ -> true | _ -> false), bindings, te))    

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

  parse_pattern leftmost >>= fun te ->
    
  option (
    surrounded (?+ blank) (?+ blank) (parse_string "with") >>= fun _ ->

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
      | None -> (
	surrounded (?* blank) (?* blank) (parse_string ":=") >>= fun _ ->
	parse_term equation_pos >>= fun value ->	
	return (NotGuarded (te, value))
      )

and parse_ifte (leftmost: Pos.t) : term Parser.t =	  

  (surrounded (?* blank) (?+ blank) (parse_string "if")) >>= fun _ ->

  parse_term leftmost >>= fun b ->

  (surrounded (?+ blank) (?+ blank) (parse_string "then")) >>= fun _ ->

  parse_term leftmost >>= fun c1 ->

  (surrounded (?+ blank) (?+ blank) (parse_string "else")) >>= fun _ ->

  parse_term leftmost >>= fun c2 ->

    return (Ifte (b, c1, c2))

and parse_lambda (leftmost: Pos.t) : term Parser.t =
  parse_string "\\" >>= fun _ ->
  ?+ blank >>= fun _ ->

  list_with_sep ~sep:(?+ blank)
    (
      try_ (parse_quantifier_lambda leftmost) 
    ) >>= fun quantifiers ->

  (surrounded (?* blank) (?* blank) (parse_string "->")) >>= fun _ ->

  parse_term leftmost >>= fun te ->
    return (Lambda (quantifiers, te))    

(* the parsing for lambda and impl quantifier is a bit different *)
and parse_quantifier (leftmost: Pos.t) nature : quantifier Parser.t = 
  list_with_sep ~sep:(?+ blank)
    (
      try_ (parse_basepattern leftmost) 
    ) >>= fun patterns ->
  
  option
    (
      ?* blank >>= fun _ ->
      parse_string "::" >>= fun _ ->
      ?* blank >>= fun _ ->
      parse_term leftmost
    ) >>= fun ty ->

  if List.length patterns = 0 then error "need at least one pattern"
  else
    return (patterns, (match ty with None -> NoAnnotation | Some ty -> Annotated ty), nature)
and parse_quantifier_lambda (leftmost: Pos.t): quantifier Parser.t =
  try_ (parse_basepattern leftmost >>= fun p -> return ([p], NoAnnotation, Explicit))
  <|> try_ (surrounded (token '(' >>= fun _ -> ?* blank >>= fun () -> return ()) (?* blank >>= fun () -> token ')') (parse_quantifier leftmost Explicit))
  <|> try_ (surrounded (token '{' >>= fun _ -> ?* blank >>= fun () -> return ()) (?* blank >>= fun () -> token '}') (parse_quantifier leftmost Hidden))
  <|> try_ (surrounded (token '[' >>= fun _ -> ?* blank >>= fun () -> return ()) (?* blank >>= fun () -> token ']') (parse_quantifier leftmost Implicit))

and parse_quantifier_impl (leftmost: Pos.t): quantifier Parser.t =
  try_ (parse_appterm leftmost >>= fun ty -> return ([PAVar AVar], Annotated ty, Explicit))
  <|> try_ (surrounded (token '(' >>= fun _ -> ?* blank >>= fun () -> return ()) (?* blank >>= fun () -> token ')') (parse_quantifier leftmost Explicit))
  <|> try_ (surrounded (token '{' >>= fun _ -> ?* blank >>= fun () -> return ()) (?* blank >>= fun () -> token '}') (parse_quantifier leftmost Hidden))
  <|> try_ (surrounded (token '[' >>= fun _ -> ?* blank >>= fun () -> return ()) (?* blank >>= fun () -> token ']') (parse_quantifier leftmost Implicit))

and  parse_declaration (leftmost: Pos.t) : declaration Parser.t =
  try_ (parse_signature leftmost)
  <|> try_ (parse_decl_equation leftmost)
  <|> try_ (parse_inductive leftmost)

and parse_signature (leftmost: Pos.t) : declaration Parser.t =
  (try_ (binop_pattern >>= fun (PCste (s, AVar)) -> return s)
   <|> (parse_name >>= fun s -> return (Name s))   
  ) >>= fun symbol ->
  
  (surrounded (?* blank) (?* blank) (parse_string "::")) >>= fun _ ->

  position >>= fun start_pos -> 

  parse_term start_pos >>= fun ty ->

  return (Signature (symbol, ty))

and parse_decl_equation (leftmost: Pos.t) : declaration Parser.t =

  parse_equation leftmost >>= fun eq -> 

  option (
    (surrounded (?* blank) (?* blank) 
       
       (position >>= fun start_pos ->       
	
	parse_string "where" >>= fun _ ->
	
	return start_pos
       )
    ) >>= fun newpos ->
    
    list_with_sep ~sep:(?* blank)
      (
	try_ (parse_declaration newpos) 
      )

  ) >>= fun decls ->  

  return (Equation (eq, match decls with | None -> [] | Some decls -> decls))

and parse_inductive (leftmost: Pos.t) : declaration Parser.t =
  (surrounded (?* blank) (?+ blank) (parse_string "inductive")) >>= fun _ ->

  (surrounded (?* blank) (?+ blank) parse_name) >>= fun name ->  

  list_with_sep ~sep:(?+ blank)
    (
      try_ (parse_quantifier_impl leftmost) 
    ) >>= fun quantifiers ->

  (surrounded (?* blank) (?* blank) (parse_string "::")) >>= fun _ ->

  position >>= fun start_pos -> 

  parse_term start_pos >>= fun ty ->

  (surrounded (?* blank) (?* blank) (parse_string ":=")) >>= fun _ ->

  option
    (
      ?* blank >>= fun _ ->
      parse_string "|" >>= fun _ ->
      ?* blank 
    ) >>= fun _ ->

  list_with_sep ~sep:(surrounded (?* blank) (?* blank) (token '|'))   
    (
      surrounded (?* blank) (?* blank) 
	(try_ (binop_pattern >>= fun (PCste (s, AVar)) -> return s)
	 <|> (parse_name >>= fun s -> return (Name s))   
	) >>= fun symbol ->
      
      (surrounded (?* blank) (?* blank) (parse_string "::")) >>= fun _ ->

      position >>= fun start_pos -> 
      
      parse_term start_pos >>= fun ty ->

      return (symbol, ty)

    ) >>= fun constructors ->

  return (Inductive (name, quantifiers, ty, constructors))

;;
