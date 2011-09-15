(*

ocamlfind ocamlopt -package spotlib,planck -c lisp.ml
ocamlfind ocamlopt -package spotlib,planck -o test lisp.cmx -linkpkg

*)
open Printf;;

type name = string;;

module NameMap = Map.Make(
  struct
    type t = name	
    let compare x y = compare x y
  end
);;

class virtual ['a] eObj =
object
  method uuid: int = 0
  method virtual get_name: string
  method virtual get_doc: string
  method virtual apply: 'a list -> (name, 'a) Hashtbl.t -> 'a
end;;

open Planck;;
module Pos = Position.File;;

(******************************************************************************)

type position = Pos.t * Pos.t
;;

type expr = Obj of expr eObj
	    | Int of int
	    | Float of float
	    | String of string
	    | Name of name
	    | Quoted of expr
	    | List of expr list
	    | SrcInfo of expr * position
;;

type lisp_error = AtPos of position * lisp_error
		  | FreeError of string * expr
		  | StringError of string
;;

exception LispException of lisp_error
;;

let rec eq e1 e2 = 
  match e1, e2 with
    | (Obj o1, Obj o2) -> o1 = o2
    | (Int i1, Int i2) -> i1 = i2
    | (Float f1, Float f2) -> f1 = f2
    | (String s1, String s2) -> s1 = s2
    | (Name n1, Name n2) -> n1 = n2
    | (Quoted e1, Quoted e2) -> eq e1 e2
    | (List l1, List l2) when List.length l1 = List.length l2 -> List.fold_left (fun acc (hd1, hd2) -> acc || eq hd1 hd2) true (List.combine l1 l2)
    | (SrcInfo (e1, _), _) -> eq e1 e2
    | (_, SrcInfo (e2, _)) -> eq e1 e2
    | _ -> false
;;

let rec equal e1 e2 = 
  match e1, e2 with
    | (Obj o1, Obj o2) when o1#get_name != "lambda" -> o1#get_name = o2#get_name 
    | (Obj o1, Obj o2) when o1#get_name = "lambda" -> o1 = o2
    | (Int i1, Int i2) -> i1 = i2
    | (Float f1, Float f2) -> f1 = f2
    | (String s1, String s2) -> s1 = s2
    | (Name n1, Name n2) -> n1 = n2
    | (Quoted e1, Quoted e2) -> equal e1 e2
    | (List l1, List l2) when List.length l1 = List.length l2 -> List.fold_left (fun acc (hd1, hd2) -> acc || equal hd1 hd2) true (List.combine l1 l2)
    | (SrcInfo (e1, _), _) -> equal e1 e2
    | (_, SrcInfo (e2, _)) -> equal e1 e2
    | _ -> false
;;

let rec extractList (e: expr) : expr list =
  match e with
    | List l -> l
    | SrcInfo (e, pos) -> (
      try extractList e with
	| LispException err -> raise (LispException (AtPos (pos, err)))
    )
    | _ -> raise (LispException (FreeError ("not a list", e)))
;;

let rec extractName ?(src: string = "" ) (e: expr) : string =
  match e with
    | Name n -> n
    | SrcInfo (e, pos) -> (
      try extractName e with
	| LispException err -> raise (LispException (AtPos (pos, err)))
    )
    | _ -> raise (LispException (FreeError (String.concat "" ["not a name("; src;")"], e)))
;;

let rec extractString (e: expr) : string =
  match e with
    | String s -> s
    | SrcInfo (e, pos) -> (
      try extractString e with
	| LispException err -> raise (LispException (AtPos (pos, err)))
    )
    | _ -> raise (LispException (FreeError ("not a string", e)))
;;

let rec unSrcInfo (e: expr) : expr =
  match e with
    | SrcInfo (e, _) -> unSrcInfo e
    | _ -> e
;;

let rec extractObj (e: expr) : expr eObj =
  match e with
    | Obj o -> o
    | SrcInfo (e, pos) -> (
      try extractObj e with
	| LispException err -> raise (LispException (AtPos (pos, err)))
    )
    | _ -> raise (LispException (FreeError ("not an object", e)))
;;

let rec extractBool (e: expr) : bool =
  match e with
    | SrcInfo (e, pos) -> extractBool e
    | List [] -> false
    | _ -> true
;;

let exprbool (b: bool) : expr =
  if b then Name "t" else List []
;;

let extractStringOrName (e: expr) : string =
  try extractString e with | _ -> extractName ~src:"extractStringOrName" e
;;

let rec extractInt (e: expr) : int =
  match e with
    | Int i -> i
    | SrcInfo (e, pos) -> (
      try extractInt e with
	| LispException err -> raise (LispException (AtPos (pos, err)))
    )
    | _ -> raise (LispException (FreeError ("not an int", e)))
;;

let rec extractFloat (e: expr) : float =
  match e with
    | Float f -> f
    | SrcInfo (e, pos) -> (
      try extractFloat e with
	| LispException err -> raise (LispException (AtPos (pos, err)))
    )
    | _ -> raise (LispException (FreeError ("not a float", e)))
;;


(******************************************************************************)

let rec expr2string (e: expr) : string =
  match e with
    | Obj o -> o#get_name
    | Int i -> string_of_int i
    | Float f -> string_of_float f
    | String s -> String.concat "" ["\""; s; "\""]
    | Name n -> n
    | Quoted e -> String.concat "" ["'"; expr2string e]
    | List [] -> "nil"
    | List l -> String.concat "" ["("; String.concat " " (List.map expr2string l); ")"]
    | SrcInfo (e, _) -> expr2string e
;;

let rec exprtype (e: expr) : string =
  match e with
    | Obj o -> "Obj"
    | Int i -> "Int"
    | Float f -> "Float"
    | String s -> "String"
    | Name n -> "Name"
    | Quoted e -> String.concat "" ["'"; exprtype e]
    | List l -> String.concat "" ["("; String.concat " " (List.map exprtype l); ")"]
    | SrcInfo (e, _) -> String.concat "" ["@"; exprtype e]
;;

open Pprinter;;

let rec intercalate l e =
  match l with
    | [] -> []
    | hd::[] -> hd::[]
    | hd1::hd2::tl-> hd1::e::(intercalate (hd2::tl) e)
;;

let rec expr2token (e: expr) : token =
  match e with
    | Obj o -> Verbatim o#get_name
    | Int i -> Verbatim (string_of_int i)
    | Float f -> Verbatim (string_of_float f)
    | String s -> Verbatim (String.concat "" ["\""; s; "\""])
    | Name n -> Verbatim n
    | Quoted e -> Box [Verbatim "'"; expr2token e]
    | List [] -> Verbatim "nil"
    | List l -> Box ([Verbatim "("] @ (intercalate (List.map (fun x -> expr2token x) l) (Space 1)) @ [Verbatim ")"])
    | SrcInfo (e, _) -> expr2token e
;;

(******************************************************************************)

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

let withPos (p: 'a Parser.t) st = begin
  position >>= fun start_pos -> 
  p >>= fun res ->
  position >>= fun end_pos ->  
    return (res, start_pos, end_pos)
end st

let blank = ignore (one_of [' '; '\t'; '\n'; '\r'])

let parse_name st = begin
  
  matched (?+ (tokenp (function | '(' | ')' | '"' | ';' | ' ' | '\t' | '\n' | '\r' | '\'' -> false | _ -> true) <?> "var")) >>= fun s2 -> 
  return s2
    
end st

let parse_string st = begin
    (matched (?+ (tokenp (function '"' -> false | _ -> true) <?> "string")) >>= fun s -> 
     return s
    )    
end st

let parse_comment st = begin
  (?* blank) >>= fun _ -> 
  token ';' >>= fun _ -> 
  (?+ (tokenp (function '\n' -> false | '\r' -> false | c -> true) <?> "comment") >>= fun _ -> 
  (?* blank) >>= fun _ -> 
   return ()
  )    
end st

let rec parse_expr st = begin
  withPos (
    try_ (parse_name >>= fun s -> 
	      if s = "nil" then return (List []) else 
		try return (Int (int_of_string s)) with
		  | _ -> try return (Float (float_of_string s)) with
		      | _ -> return (Name s)
    )
    <|> try_ (token '"' >>= fun _ -> parse_string >>= fun s -> token '"' >>= fun _ -> return (String s))
    <|> try_ (token '\'' >>= fun _ -> parse_expr >>= fun e -> return (Quoted e))
    <|> try_ (token '(' >>= fun _ -> token ')' >>= fun _ -> return (List []))
    <|> try_ (surrounded 
		(token '(' >>= fun _ -> ?* (blank <|> parse_comment) >>= fun () -> return ()) 
		(?* (blank <|> parse_comment) >>= fun () -> token ')') 
		(list_with_sep 
		   ~sep:(?+ blank) 
		   parse_expr
		) >>= fun l -> return (List l)
    )	   
    <|> try_ ((?+ blank) >>= fun _ ->  parse_expr)
    <|> try_ (parse_comment >>= fun _ -> parse_expr)
  ) >>= fun (e, startp, endp) ->  
  return (SrcInfo (e, (startp, endp)))

end st
;; 

let parse_oneexpr st = begin
  parse_expr >>= fun expr ->
  position >>= fun pos ->
  return (pos.Pos.byte, expr)
end st
;;

let parse_exprs st = begin
  (list_with_sep 
     ~sep:(?* blank <|> parse_comment)
     parse_expr
  ) >>= fun exprs ->
  position >>= fun pos ->
  return (pos.Pos.byte, exprs)
end st
;;

(******************************************************************************)

type env = (name, expr) Hashtbl.t
;;

let rec eval (e: expr) (ctxt: env) : expr =
  (*printf "%s\n" (expr2string e);*)
  match e with
    | SrcInfo (e, pos) -> (
      try
	eval e ctxt
      with
	| LispException err -> raise (LispException (AtPos (pos, err)))
	(*| _ -> raise Pervasives.Exit*)
    )    
    | Obj _ as o -> o
    | Int _ as i -> i
    | Float _ as f -> f
    | String _ as s -> s
    | Quoted e -> e
    | Name n -> (
      try 
	Hashtbl.find ctxt n
      with
	| Not_found -> raise (LispException (FreeError ("unknown name", e)))
    )
    | List [] -> List []
    | List ((Obj o)::tl) -> o#apply tl ctxt
    | List (hd::tl) -> 
      let hd' = eval hd ctxt in
      if hd = hd' then
	raise (LispException (FreeError ("not a function", hd)))
      else
	eval (List (hd'::tl)) ctxt
;;

(*********************************)

let rec drop (l: 'a list) (n: int) : 'a list =
  match n with 
    | 0 -> l
    | _ -> drop (List.tl l) (n-1)
;;

let restorevals (l: name list) (ctxt: env) : unit =
    List.fold_left (fun acc hd -> 
      Hashtbl.remove ctxt hd
    ) () l
;;

let save_and_restore (l: name list) (ctxt: env) (f: unit -> 'a) : 'a =
  let res = 
    try
      f ()
    with
      | e -> restorevals l ctxt; raise e
  in  
  restorevals l ctxt;
  res
;;

class lambda (name: string) (doc: string) (listargs: (name * expr option) list) (body: expr list) =
object (self)
  inherit [expr] eObj
  method uuid = 1
  method get_name = name
  method get_doc = doc
  method apply args ctxt =     
  
    let args = args @ List.map (fun (name, value) -> 
      match value with
	| None -> raise (LispException (StringError "not enough arguments (or missing default value)"))
	| Some value -> eval value ctxt
    ) (drop listargs (List.length args)) in
      
    save_and_restore (fst (List.split listargs)) ctxt (
      fun _ -> 
    
	let args' = List.map (fun e -> eval e ctxt) args in
    
	let _ = List.map (fun ((n, _), v) -> 
	  Hashtbl.add ctxt n v 
	) (List.combine listargs args') in
    
	List.fold_left (fun acc expr -> eval expr ctxt) (List []) body
    )
end;;

class defun =
object (self)
  inherit [expr] eObj
  method uuid = 2
  method get_name = "defun"
  method get_doc = "primitive to define a function\nformat:\n(defun name (params) \"doc\" body"
  method apply args ctxt =     
    if List.length args != 4 then
      raise (LispException (StringError "wrong number of arguments"))
    else
           
      let listargs = 
	let l = extractList (List.nth args 1) in
	List.map (fun hd -> 
	  try 
	    (extractName ~src:"defun(1)" hd, None)
	  with
	    | _ -> (
	      try 
		let [argname; defaultvalue] = extractList hd in
		(extractName ~src:"defun(2)" argname, Some defaultvalue)
	      with
		| _ -> raise (LispException (FreeError ("wrong argument form", hd)))
	    )
	) l
      in 
      let body = drop args 2 in
      let name = extractName ~src:"defun(3)" (List.hd args) in
      let doc = extractString (List.nth args 2) in
      let o = Obj (new lambda name doc listargs body) in
      Hashtbl.replace ctxt name o;
      o

end;;

class plus =
object (self)
  inherit [expr] eObj
  method uuid = 3
  method get_name = "+"
  method get_doc = "sum its arguments"
  method apply args ctxt =     
    let args' = List.map (fun e -> eval e ctxt) args in
    List.fold_left (fun acc hd ->
      match acc, (unSrcInfo hd) with
	| (Int sum, Int a) -> Int (sum + a)
	| (Int sum, Float a) -> Float (float sum +. a)
	| (Float sum, Int a) -> Float (sum +. float a)
	| (Float sum, Float a) -> Float (sum +. a)
	| _ -> raise (LispException (FreeError (String.concat "" ["neither an int or a float ("; exprtype hd; ")"], hd)))
    ) (Int 0) args'
end;;

class mult =
object (self)
  inherit [expr] eObj
  method uuid = 4
  method get_name = "*"
  method get_doc = "product its arguments"
  method apply args ctxt =     
    let args' = List.map (fun e -> eval e ctxt) args in
    List.fold_left (fun acc hd ->
      match acc, (unSrcInfo hd) with
	| (Int sum, Int a) -> Int (sum * a)
	| (Int sum, Float a) -> Float (float sum *. a)
	| (Float sum, Int a) -> Float (sum *. float a)
	| (Float sum, Float a) -> Float (sum *. a)
	| _ -> raise (LispException (FreeError (String.concat "" ["neither an int or a float ("; exprtype hd; ")"], hd)))
    ) (Int 1) args'
end;;

class getdoc =
object (self)
  inherit [expr] eObj
  method uuid = 5
  method get_name = "getdoc"
  method get_doc = "return the documentation of the function symbol passed as argument"
  method apply args ctxt =     
    if List.length args != 1 then
      raise (LispException (StringError "wrong number of arguments"))
    else
      let n = extractName ~src:"getdoc(1)" (List.nth args 0) in
      let value = try Hashtbl.find ctxt n with | Not_found -> raise (LispException (FreeError ("unknown name", (List.nth args 0)))) in
      let o = extractObj value in
      String o#get_doc
end;;

class elet =
object (self)
  inherit [expr] eObj
  method uuid = 6
  method get_name = "let"
  method get_doc = "lisp let expression\n format: (let varlist body)\n with varlist := ((var0 val0) ... (vari vali))"
  method apply args ctxt =     
  
    if List.length args < 2 then
      raise (LispException (StringError "not enough arguments for let"))
    else
      let vars = 
	try 
	  let l = extractList (List.nth args 0) in
	  List.map (fun hd ->
	    try 
	      let [var; value] = extractList hd in
	      let n = extractName ~src:"elet(1)" var in
	      (n, value)
	    with
	      | _ -> 
		let n = extractName ~src:"elet(2)" hd in
		(n, List [])
	  ) l
	with
	  | _ -> raise (LispException (FreeError ("this is an improper list of bindings for let", List.nth args 0)))
      in
      
      save_and_restore (fst (List.split vars)) ctxt (
	fun _ -> 
    
	  let _ = List.map (fun (n, value) -> 
	    Hashtbl.add ctxt n (eval value ctxt)
	  ) vars in    
	  
	  let body = drop args 1 in
	  
	  List.fold_left (fun acc expr -> eval expr ctxt) (List []) body
      )
end;;

class set =
object (self)
  inherit [expr] eObj
  method uuid = 7
  method get_name = "set"
  method get_doc = "set a variable to a value\nformat: (set var value)\nN.B.: both args are evaluated prior to mutation"
  method apply args ctxt =     
    if List.length args != 2 then
      raise (LispException (StringError "wrong number of arguments"))
    else
      let [var; value] = List.map (fun hd -> eval hd ctxt) args in
      let n = extractName ~src:"set(1)" var in
      Hashtbl.replace ctxt n value;
      value      
end;;

class setq =
object (self)
  inherit [expr] eObj
  method uuid = 8
  method get_name = "setq"
  method get_doc = "set a variable to a value\nformat: (set var value)\nN.B.: only value is evaluated prior to mutation"
  method apply args ctxt =     
    if List.length args != 2 then
      raise (LispException (StringError "wrong number of arguments"))
    else
      let [var; value] = args in
      let value = eval value ctxt in
      let n = extractName ~src:"setq(1)" var in
      Hashtbl.replace ctxt n value;
      value      
end;;

class ifte =
object (self)
  inherit [expr] eObj
  method uuid = 9
  method get_name = "if"
  method get_doc = "conditional branching\nformat (if test then ?else)"
  method apply args ctxt =     
    if List.length args < 2 || List.length args > 3 then
      raise (LispException (StringError "wrong number of arguments"))
    else
      if extractBool (eval (List.nth args 0) ctxt) then
	eval (List.nth args 1) ctxt else
	if List.length args = 2 then List [] else eval (List.nth args 2) ctxt
end;;

class ewhen =
object (self)
  inherit [expr] eObj
  method uuid = 10
  method get_name = "when"
  method get_doc = "(when COND BODY...)

If COND yields non-nil, do BODY, else return nil.
When COND yields non-nil, eval BODY forms sequentially and return
value of last one, or nil if there are none.
"
  method apply args ctxt =     
    if List.length args < 1 then
      raise (LispException (StringError "wrong number of arguments"))
    else
      if extractBool (eval (List.nth args 0) ctxt) then 
	List.fold_left (fun acc hd -> eval hd ctxt) (List []) (List.tl args) 
      else (List [])
end;;

let rec fold_left_stop (f: 'b -> 'a option) (l: 'a list) : 'b option =
  match l with
    | [] -> None
    | hd::tl -> 
      match f hd with
	| None -> fold_left_stop f tl
	| res -> res
;;

class cond =
object (self)
  inherit [expr] eObj
  method uuid = 11
  method get_name = "cond"
  method get_doc = "(cond CLAUSES...)

Try each clause until one succeeds.
Each clause looks like (CONDITION BODY...).  CONDITION is evaluated
and, if the value is non-nil, this clause succeeds:
then the expressions in BODY are evaluated and the last one's
value is the value of the cond-form.
If no clause succeeds, cond returns nil.
If a clause has one element, as in (CONDITION),
CONDITION's value if non-nil is returned from the cond-form.
"
  method apply args ctxt =     
    let res =
      fold_left_stop (fun hd -> 
	let l = extractList hd in
	match l with
	  | [] -> None
	  | hd::tl ->
	    if extractBool (eval hd ctxt) then
	      Some (List.fold_left (fun acc hd -> eval hd ctxt) (List []) tl)
	    else None
      ) args in
    match res with
      | None -> List []
      | Some res -> res
end;;

class eTrue =
object (self)
  inherit [expr] eObj
  method uuid = 12
  method get_name = "t"
  method get_doc = "true value"
  method apply args ctxt = 
    raise (LispException (StringError "not executable"))
end;;

class eEq =
object (self)
  inherit [expr] eObj
  method uuid = 13
  method get_name = "="
  method get_doc = "numerical equality"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (LispException (StringError "wrong number of arguments"))
     else
       match List.map (fun hd -> eval hd ctxt) args with
	 | [Int i1; Int i2] -> exprbool (i1 = i2)
	 | [Int i1; Float f2] -> exprbool (float i1 = f2)
	 | [Float f1; Int i2] -> exprbool (f1 = float i2)
	 | [Float f1; Float f2] -> exprbool (f1 = f2)
	 | _ -> raise (LispException (StringError "not numerical arguments"))
end;;

class eGt =
object (self)
  inherit [expr] eObj
  method uuid = 14
  method get_name = ">"
  method get_doc = "numerical Gt"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (LispException (StringError "wrong number of arguments"))
     else
       match List.map (fun hd -> eval hd ctxt) args with
	 | [Int i1; Int i2] -> exprbool (i1 > i2)
	 | [Int i1; Float f2] -> exprbool (float i1 > f2)
	 | [Float f1; Int i2] -> exprbool (f1 > float i2)
	 | [Float f1; Float f2] -> exprbool (f1 > f2)
	 | _ -> raise (LispException (StringError "not numerical arguments"))
end;;

class eGe =
object (self)
  inherit [expr] eObj
  method uuid = 15
  method get_name = ">="
  method get_doc = "numerical Ge"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (LispException (StringError "wrong number of arguments"))
     else
       match List.map (fun hd -> eval hd ctxt) args with
	 | [Int i1; Int i2] -> exprbool (i1 >= i2)
	 | [Int i1; Float f2] -> exprbool (float i1 >= f2)
	 | [Float f1; Int i2] -> exprbool (f1 >= float i2)
	 | [Float f1; Float f2] -> exprbool (f1 >= f2)
	 | _ -> raise (LispException (StringError "not numerical arguments"))
end;;

class eLt =
object (self)
  inherit [expr] eObj
  method uuid = 16
  method get_name = "<"
  method get_doc = "numerical Lt"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (LispException (StringError "wrong number of arguments"))
     else
       match List.map (fun hd -> eval hd ctxt) args with
	 | [Int i1; Int i2] -> exprbool (i1 < i2)
	 | [Int i1; Float f2] -> exprbool (float i1 < f2)
	 | [Float f1; Int i2] -> exprbool (f1 < float i2)
	 | [Float f1; Float f2] -> exprbool (f1 < f2)
	 | _ -> raise (LispException (StringError "not numerical arguments"))
end;;

class eLe =
object (self)
  inherit [expr] eObj
  method uuid = 17
  method get_name = "<="
  method get_doc = "numerical Le"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (LispException (StringError "wrong number of arguments"))
     else
       match List.map (fun hd -> eval hd ctxt) args with
	 | [Int i1; Int i2] -> exprbool (i1 <= i2)
	 | [Int i1; Float f2] -> exprbool (float i1 <= f2)
	 | [Float f1; Int i2] -> exprbool (f1 <= float i2)
	 | [Float f1; Float f2] -> exprbool (f1 <= f2)
	 | _ -> raise (LispException (StringError "not numerical arguments"))
end;;

class eeq =
object (self)
  inherit [expr] eObj
  method uuid = 18
  method get_name = "eq"
  method get_doc = "strict equality"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (LispException (StringError "wrong number of arguments"))
     else
       let [e1; e2] = List.map (fun hd -> eval hd ctxt) args in
       exprbool (eq e1 e2)
end;;

class eequal =
object (self)
  inherit [expr] eObj
  method uuid = 19
  method get_name = "equal"
  method get_doc = "equiv equality"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (LispException (StringError "wrong number of arguments"))
     else
       let [e1; e2] = List.map (fun hd -> eval hd ctxt) args in
       exprbool (equal e1 e2)
end;;

class estringlt =
object (self)
  inherit [expr] eObj
  method uuid = 20
  method get_name = "string<"
  method get_doc = "string lt"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (LispException (StringError "wrong number of arguments"))
     else
       let [s1; s2] = List.map (fun hd -> 
	 let hd' = eval hd ctxt in
	 try extractString hd' with | _ -> extractName ~src:"estringlt(1)" hd'
       ) args in
       exprbool (s1 < s2)
end;;

class estringlessp =
object (self)
  inherit estringlt
  method get_name = "string-lessp"
end;;

class estringeq =
object (self)
  inherit [expr] eObj
  method uuid = 21
  method get_name = "string="
  method get_doc = "string eq"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (LispException (StringError "wrong number of arguments"))
     else
       let [s1; s2] = List.map (fun hd -> 
	 let hd' = eval hd ctxt in
	 extractStringOrName hd'
       ) args in
       exprbool (s1 = s2)
end;;

class estringequal =
object (self)
  inherit estringlt
  method uuid = 22
  method get_name = "string-equal"
end;;

let parse_common : string Parser.t =
  matched (?+ (tokenp (function |'\\' | '%' -> false | _ -> true) <?> "common")) >>= fun s -> 
  return s
;;

let parse_formatter args : string Parser.t =
  token '%' >>= fun _ ->
  (token_result (function 
    | 's' -> ( 
      try 
	let s = extractStringOrName (List.hd !args) in
	args := List.tl !args;
	Result.Ok s
      with
	| _ -> Result.Error (String.concat "" ["not a symbol or string: "; expr2string (List.hd !args)])
    )
    | 'd' -> (
      try 
	let s = 
	  try 
	    string_of_int (extractInt (List.hd !args))
	  with
	    | _ -> string_of_float (extractFloat (List.hd !args))
	in
	args := List.tl !args;
	Result.Ok s
      with
	| _ -> Result.Error (String.concat "" ["not a numerical: "; expr2string (List.hd !args)])
    )
    | 'c' -> Result.Error "NYI"
    | c -> Result.Error (String.concat "" ["unknown formater: "; String.make 1 c])
   )
  ) >>= fun res -> 
  return res
;;

let parse_escaped : string Parser.t =
  matched (
    token '\\' >>= fun _ ->
    tokenp (fun _ -> true) >>= fun _ ->
    return ()
  ) >>= fun s ->
  match s with
    | "\\n" -> return "\n"
    | "\\t" -> return "\t"
    | "\\r" -> return "\r"
;;

(* I cannot managed to properly grab the error from parse_formatter ... grrr*)
let parse_msg args : (string list) Parser.t =
  (?** (parse_common <|> (parse_formatter args) <|> parse_escaped)) >>= fun l ->
  eos >>= fun _ ->
  return l
;;

class message =
object (self)
  inherit [expr] eObj
  method uuid = 23
  method get_name = "message"
  method get_doc = "format a message"
  method apply args ctxt = 
     if List.length args < 1 then
       raise (LispException (StringError "wrong number of arguments"))
     else
       let args = List.map (fun hd -> eval hd ctxt) args in
       let msg = extractString (List.hd args) in
       let args = ref (List.tl args) in
       let stream = Stream.from_string ~filename:"stdin" msg in
       match parse_msg args stream with
	 | Result.Ok (res, _) -> 
	   let s = (String.concat "" res) in
	   printf "%s" s;
	   String s
	 | Result.Error (pos, s) ->
	   raise (LispException (StringError (String.concat "\n" ["in:"; msg; 
								  String.concat "" ["error @"; 
										    string_of_int (pos.Pos.line); 
										    ":"; 
										    string_of_int (pos.Pos.column); 
										   ]; 
								  s])))

end;;

class print =
object (self)
  inherit [expr] eObj
  method uuid = 24
  method get_name = "print"
  method get_doc = "print an expr"
  method apply args ctxt = 
     if List.length args < 1 then
       raise (LispException (StringError "wrong number of arguments"))
     else
       let e = eval (List.hd args) ctxt in
       let s = box2string (token2box (expr2token e) 400 2) in
       printf "%s\n" s;
       String s
end;;

class econs =
object (self)
  inherit [expr] eObj
  method uuid = 25
  method get_name = "cons"
  method get_doc = "constructor"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (LispException (StringError "wrong number of arguments"))
     else
       let [e1; e2] = List.map (fun hd -> eval hd ctxt) args in
       let l = extractList e2 in
       List (e1::l)
end;;

class ecar =
object (self)
  inherit [expr] eObj
  method uuid = 26
  method get_name = "car"
  method get_doc = "extract head of list"
  method apply args ctxt = 
     if List.length args != 1 then
      raise (LispException (StringError "wrong number of arguments"))
     else
       let [e] = List.map (fun hd -> eval hd ctxt) args in
       let l = extractList e in
       match l with
	 | [] -> List []
	 | hd::tl -> hd
end;;

class ecdr =
object (self)
  inherit [expr] eObj
  method uuid = 27
  method get_name = "cdr"
  method get_doc = "extract tail of list"
  method apply args ctxt = 
     if List.length args != 1 then
      raise (LispException (StringError "wrong number of arguments"))
     else
       let [e] = List.map (fun hd -> eval hd ctxt) args in
       let l = extractList e in
       match l with
	 | [] -> List []
	 | hd::tl -> List tl
end;;

class enthcdr =
object (self)
  inherit [expr] eObj
  method uuid = 28
  method get_name = "nthcdr"
  method get_doc = "correspond to nth call to cdr"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (LispException (StringError "wrong number of arguments"))
     else
       let [e1; e2] = List.map (fun hd -> eval hd ctxt) args in
       let l = extractList e2 in
       let n = extractInt e1 in
       if List.length l <= n then List [] else List (drop l n)
end;;

class enth =
object (self)
  inherit [expr] eObj
  method uuid = 29
  method get_name = "nth"
  method get_doc = "returns the nth element of a list"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (LispException (StringError "wrong number of arguments"))
     else
       let [e1; e2] = List.map (fun hd -> eval hd ctxt) args in
       let l = extractList e2 in
       let n = extractInt e1 in
       if List.length l <= n then List [] else List.nth l n
end;;

class setcar =
object (self)
  inherit [expr] eObj
  method uuid = 30
  method get_name = "setcar"
  method get_doc = "mutate the variable, replacing its head"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (LispException (StringError "wrong number of arguments"))
     else
       let value = eval (List.nth args 1) ctxt in
       let n = extractName ~src:"setcar(1)" (List.nth args 0) in
       let nvalue = 
	 try 
	   Hashtbl.find ctxt n
	 with
	   | Not_found -> raise (LispException (FreeError ("unknown name", Name n)))
       in 
       let nl = extractList nvalue in
       match nl with
	 | [] -> raise (LispException (StringError ("the variable has for value nil")))
	 | hd::tl -> let nvalue = List (value::tl) in
		     Hashtbl.replace ctxt n nvalue;
		     value

end;;

class setcdr =
object (self)
  inherit [expr] eObj
  method uuid = 31
  method get_name = "setcdr"
  method get_doc = "mutate the variable, replacing its tail"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (LispException (StringError "wrong number of arguments"))
     else
       let value = extractList (eval (List.nth args 1) ctxt) in
       let n = extractName ~src:"setcdr(1)" (List.nth args 0) in
       let nvalue = 
	 try 
	   Hashtbl.find ctxt n 
	 with
	   | Not_found -> raise (LispException (FreeError ("unknown name", Name n)))
       in 
       let nl = extractList nvalue in
       match nl with
	 | [] -> raise (LispException (StringError ("the variable has for value nil")))
	 | hd::tl -> let nvalue = List (hd::value) in
		     Hashtbl.replace ctxt n nvalue;
		     List value

end;;

class length =
object (self)
  inherit [expr] eObj
  method uuid = 32
  method get_name = "length"
  method get_doc = "(length SEQUENCE)

Return the length of vector, list or string SEQUENCE.
A byte-code function object is also allowed.
If the string contains multibyte characters, this is not necessarily
the number of bytes in the string; it is the number of characters.
To get the number of bytes, use `string-bytes'.
"
  method apply args ctxt = 
     if List.length args != 1 then
      raise (LispException (StringError "wrong number of arguments"))
     else
       let e = eval (List.hd args) ctxt in
       Int (
	 try List.length (extractList e) with
	   | _ -> String.length (extractString e)
       )
end;;

class symbolname =
object (self)
  inherit [expr] eObj
  method uuid = 33
  method get_name = "symbol-name"
  method get_doc = "(symbol-name SYMBOL)

Return SYMBOL's name, a string.
"
  method apply args ctxt = 
     if List.length args != 1 then
      raise (LispException (StringError "wrong number of arguments"))
     else
       String (extractName ~src:"symbolname(1)" (eval (List.hd args) ctxt))
end;;


class enot =
object (self)
  inherit [expr] eObj
  method uuid = 34
  method get_name = "not"
  method get_doc = "negation"
  method apply args ctxt = 
     if List.length args != 1 then
      raise (LispException (StringError "wrong number of arguments"))
     else
       exprbool (not (extractBool (eval (List.nth args 0) ctxt)))
end;;

class ewhile =
object (self)
  inherit [expr] eObj
  method uuid = 35
  method get_name = "while"
  method get_doc = "while loop\nformat: (while test body...)"
  method apply args ctxt = 
     if List.length args < 1 then
      raise (LispException (StringError "wrong number of arguments"))
     else
       let test = List.hd args in
       let body = List.tl args in
       let res = ref (List []) in
       while extractBool (eval test ctxt) do
	 res := List.fold_left (fun acc hd -> eval hd ctxt) (List []) body
       done;      
       !res
end;;

class dolist =
object (self)
  inherit [expr] eObj
  method uuid = 36
  method get_name = "dolist"
  method get_doc = "(dolist (VAR LIST [RESULT]) BODY...)\nLoop over a list.\nEvaluate BODY with VAR bound to each car from LIST, in turn.\nThen evaluate RESULT to get return value, default nil.\n"
  method apply args ctxt = 
     if List.length args < 2 then
      raise (LispException (StringError "wrong number of arguments"))
     else
       let param = List.hd args in
       let body = List.tl args in
       let [var; list; result] = extractList param in
       let var = extractName ~src:"dolist(1)" var in
       let list = extractList (eval list ctxt) in
       let result = extractName result in
       
       save_and_restore [var] ctxt (
	 fun _ -> 

	   let _ = List.fold_left (fun acc hd -> 
	     Hashtbl.add ctxt var hd;
	     Pervasives.ignore(List.fold_left (fun acc hd -> Pervasives.ignore(eval hd ctxt)) () body)
	   ) () list in
	   try Hashtbl.find ctxt result with _ -> List []
       )
end;;

let rec from_to (from: int) (ito: int) : int list =
  if from > ito then [] else from::(from_to (from+1) ito)
;;

class dotimes =
object (self)
  inherit [expr] eObj
  method uuid = 37
  method get_name = "dotimes"
  method get_doc = "
(dotimes (VAR COUNT [RESULT]) BODY...)

Loop a certain number of times.
Evaluate BODY with VAR bound to successive integers running from 0,
inclusive, to COUNT, exclusive.  Then evaluate RESULT to get
the return value (nil if RESULT is omitted)."
  method apply args ctxt = 
     if List.length args < 2 then
      raise (LispException (StringError "wrong number of arguments"))
     else
       let param = List.hd args in
       let body = List.tl args in
       let [var; count; result] = extractList param in
       let var = extractName var in
       let count = extractInt (eval count ctxt) in
       let result = extractName result in

       save_and_restore [var] ctxt (
	 fun _ ->

	   let _ = List.fold_left (fun acc hd -> 
	     Hashtbl.add ctxt var (Int hd);
	     Pervasives.ignore(List.fold_left (fun acc hd -> Pervasives.ignore(eval hd ctxt)) () body)
	   ) () (from_to 0 count) in
	   try Hashtbl.find ctxt result with _ -> List []
       )
end;;

class plusone =
object (self)
  inherit [expr] eObj
  method uuid = 38
  method get_name = "1+"
  method get_doc = "(1+ NUMBER)

Return NUMBER plus one.  NUMBER may be a number or a marker.
Markers are converted to integers."
  method apply args ctxt = 
     if List.length args != 1 then
      raise (LispException (StringError "wrong number of arguments"))
     else
       try 
	 let i = extractInt (eval (List.nth args 0) ctxt) in
	 Int (i + 1)
       with
	 | _ -> 
	   try 
	     let f = extractFloat (eval (List.nth args 0) ctxt) in
	     Float (f +. 1.)
	   with
	     | _ -> raise (LispException (FreeError ("not a numerical", List.nth args 0)))

end;;

class minusone =
object (self)
  inherit [expr] eObj
  method uuid = 39
  method get_name = "1-"
  method get_doc = "(1- NUMBER)

Return NUMBER minus one.  NUMBER may be a number or a marker.
Markers are converted to integers."
  method apply args ctxt = 
     if List.length args != 1 then
      raise (LispException (StringError "wrong number of arguments"))
     else
       try 
	 let i = extractInt (eval (List.nth args 0) ctxt) in
	 Int (i - 1)
       with
	 | _ -> 
	   try 
	     let f = extractFloat (eval (List.nth args 0) ctxt) in
	     Float (f -. 1.)
	   with
	     | _ -> raise (LispException (FreeError ("not a numerical", List.nth args 0)))

end;;


let int2string (i: int) (size: int) : string =
  let s = string_of_int i in
  if String.length s > size then
    raise (Failure "int2string: string rep. to long")
  else
    if String.length s < size then (
      let prefix = String.make (size - String.length s) '0' in
      String.concat "" [prefix; s]
    ) else s
;;

open Unix;;

class currenttimestring =
object (self)
  inherit [expr] eObj
  method uuid = 40
  method get_name = "current-time-string"
  method get_doc = "simple version without args"
  method apply args ctxt = 
     if List.length args != 0 then
      raise (LispException (StringError "wrong number of arguments"))
     else
       let mtm = localtime (time ()) in
       String (
	 String.concat " " [
	   (match mtm.tm_wday with
	     | 0 -> "Sun"
	     | 1 -> "Mon"
	     | 2 -> "Tue"
	     | 3 -> "Wed"
	     | 4 -> "Thu"
	     | 5 -> "Fri"
	     | 6 -> "Sat"
	   );
	   (match mtm.tm_mon with
	     | 0 -> "Jan"
	     | 1 -> "Feb"
	     | 2 -> "Mar"
	     | 3 -> "Apr"
	     | 4 -> "May"
	     | 5 -> "Jun"
	     | 6 -> "Jul"
	     | 7 -> "Aug"
	     | 8 -> "Sep"
	     | 9 -> "Oct"
	     | 10 -> "Nov"
	     | 11 -> "Dec"
	   );
	   int2string mtm.tm_mday 2;
	   String.concat ":" [int2string mtm.tm_hour 2; int2string mtm.tm_min 2; int2string mtm.tm_sec 2];
	   int2string (mtm.tm_year + 1900) 4;
	 ]
       )

end;;

class elist =
object (self)
  inherit [expr] eObj
  method uuid = 41
  method get_name = "list"
  method get_doc = "returns its args in a list"
  method apply args ctxt = 
    List (List.map (fun hd -> eval hd ctxt) args)
end;;

class progn =
object (self)
  inherit [expr] eObj
  method uuid = 42
  method get_name = "progn"
  method get_doc = "(progn BODY...)

Eval BODY forms sequentially and return value of last one."
  method apply args ctxt = 
    List.fold_left (fun acc hd -> 
      eval hd ctxt) (List []) args
end;;


(******************************************************************************)

let primitives = [new plus; new mult; new plusone; new minusone;
		  new defun;
		  new getdoc;
		  new elet;
		  new set;
		  new setq;
		  new ifte; new ewhen; new cond;
		  new eTrue;
		  new eEq; new eLt; new eLe; new eGt; new eGe;
		  new eeq; new eequal;
		  new estringlt; new estringlessp; new estringeq; new estringequal;
		  new message; new print;
		  new econs; new ecar; new ecdr; new enthcdr; new enth; new setcar; new setcdr; new elist;
		  new length; new symbolname;
		  new currenttimestring;
		  new enot;
		  new ewhile; new dolist; new dotimes;
		  new progn;
		 ];;

let init_ctxt () = 
  let ctxt = Hashtbl.create 100 in
  List.fold_left (fun acc o -> 
    Hashtbl.replace ctxt o#get_name (Obj o)
  ) () primitives;
  ctxt;;

let rec execException2box (e: lisp_error) : token =
  match e with
    | StringError s -> Verbatim s
    | FreeError (s, e) -> Box [Verbatim s; Verbatim ":"; Space 1; Verbatim "'"; expr2token e; Verbatim "'"; Space 1; Verbatim "::"; Space 1; Verbatim (exprtype e)]
    | AtPos (_, ((AtPos _) as e)) -> execException2box e
    | AtPos ((startp, endp), e) -> Box [Verbatim (string_of_int (startp.Pos.line)); 
					Verbatim ":"; 
					Verbatim (string_of_int (startp.Pos.column)); 
					Verbatim "-"; 
					Verbatim (string_of_int (endp.Pos.line)); 
					Verbatim ":"; 
					Verbatim (string_of_int (endp.Pos.column)); 
					Space 1;
					Verbatim ":"; 
					Space 1;
					execException2box e;
				       ]
;;

let interp_expr ?(verbose: bool = false) ctxt expr = 
  (*printf "term = '%s'\n" s;*)
  let stream = Stream.from_string ~filename:"stdin" expr in
  match parse_oneexpr stream with
    | Result.Ok ((consume, res), _) -> (
      let res' = eval res ctxt in
      if verbose then printbox (token2box (expr2token res') 400 2);
      (consume, res')
    )
    | Result.Error (pos, s) ->
      Format.eprintf "%s\n%a: syntax error: %s@." expr Position.File.format pos s;      
      raise (LispException (StringError (String.concat "\n" ["Parsing error:"; s])))
;;

let interp_exprs ctxt expr = 
  (*printf "term = '%s'\n" s;*)
  let stream = Stream.from_string ~filename:"stdin" expr in
  match parse_exprs stream with
    | Result.Ok ((consume, res), _) -> (
      let res' = List.map (fun hd -> eval hd ctxt) res in
      (consume, res')
    )
    | Result.Error (pos, s) ->
      Format.eprintf "%s\n%a: syntax error: %s@." expr Position.File.format pos s;      
      raise (LispException (StringError (String.concat "\n" ["Parsing error:"; s])))
;;

let interp_file ctxt filename = 
  let ic = Pervasives.open_in filename in
  let stream = Stream.from_chan ~filename:filename ic in
  let parse =   
    parse_exprs >>= fun (_, exprs) ->
    ?* blank <|> parse_comment >>= fun _ ->
    eos >>= fun _ ->
    return exprs in
  match parse stream with
    | Result.Ok (res, _) -> (
      let _ = List.map (fun hd -> 
	eval hd ctxt
      ) res in
      close_in ic
    )
    | Result.Error (pos, s) ->
      Format.eprintf "%s\n%a: syntax error: %s@." filename Position.File.format pos s;      
      close_in ic;
      raise (LispException (StringError (String.concat "\n" ["Parsing error:"; s])))
	
;;

let interp_stdin ctxt =
  let finished = ref false in
  let terms = ref [] in
  let parse =
    eos_as_none (parse_oneexpr >>= fun (_, expr) -> return expr) in      
  while not !finished do
    ( 
      printf "mylisp> "; flush Pervasives.stdout;
      let stream = Stream.from_chan ~filename:"stdin" Pervasives.stdin in
      match parse stream with
	| Result.Ok (Some res, _) -> (	  
	  try (
	    (* we evaluate the term *)
	    let res' = eval res ctxt in
	    (* we save it *)
	    terms := res::!terms;
	    (* and show the result *)	    
	    printf "\nresult:\n";
	    printbox (token2box (expr2token res') 400 2);
	    printf "\n";
	    flush Pervasives.stdout
	  ) with
	    | LispException err -> printf "%s\n" (box2string (token2box (execException2box err) 400 2))
	)
	| Result.Ok (None, _) -> (
	  (* we are done *)
	  (* before leaving the loop, let's save the terms at the end of the file *)
	  let _ = (
	    try 
	      let terms = List.rev !terms in
	      let oc = open_out "saved-interactive-session.lisp" in
	      seek_out oc (out_channel_length oc);
	      let _ = List.map (fun hd -> 
		output_string oc (box2string (token2box (expr2token hd) 400 2));
		output_string oc "\n\n"
	      ) terms in
	      close_out oc
	    with
	      | Sys_error _ -> ()
	  ) in
	  printf "\n"; 
	  finished := true;	  
	  flush Pervasives.stdout
	)
	| Result.Error (pos, s) ->
	  Format.eprintf "%a: syntax error: %s@." Position.File.format pos s
    )
  done

;;
	  

(******************************************************************************)

open Lang_intf;;

(*

  we implement a module of signature Lang for lisp
  
*)

module LispLang : Lang =
struct
  type value = expr      
  type ltype = string
  type session = env

  type error = lisp_error

  exception Exception = LispException

  let error2string err = box2string (token2box (execException2box err) 400 2);;

  let name = "Lisp";;

  let empty_session () =  init_ctxt () ;;

  let proceed_expr session exprs = 
    interp_expr ~verbose:true session exprs 
  ;;

  let proceed_exprs session exprs = 
    interp_exprs session exprs
  ;;

  let proceed_file session filename =
    interp_file session filename
  ;;

  let print session value = 
    box2string (token2box (expr2token value) 400 2);
  ;;

  (* return the type of a value *)
  let get_type session value = 
    exprtype value
  ;;

  (* retrieve a value by name *) 
  let lookup session n =
    try 
      Hashtbl.find session n
    with
      | Not_found -> raise (LispException (FreeError ("unknown name", Name n)))
  ;;

  (* fold : ('a -> 'b -> 'c -> 'c) -> ('a, 'b) t -> 'c -> 'c *)
  (* returns the set of defined names in a session *)
  let get_defs session =
    Hashtbl.fold (fun k value acc -> 
      (k, exprtype value)::acc
    ) session []
  ;;

  (* the main features of language: application *)
  let apply session fct args = 
    let e = List (fct::args) in
    eval e session
  ;;

end;;



(******************************************************************************)


