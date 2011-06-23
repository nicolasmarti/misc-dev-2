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
  method virtual get_name: string
  method virtual get_doc: string
  method virtual apply: 'a list -> ('a NameMap.t) ref -> 'a
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
    <|> try_ (surrounded (?+ blank) (?* blank) parse_expr)
    <|> try_ (parse_comment >>= fun _ -> parse_expr)
  ) >>= fun (e, startp, endp) ->
  return (SrcInfo (e, (startp, endp)))

end st
;; 


let parse_exprs st = begin
  (list_with_sep 
     ~sep:(?* blank <|> parse_comment <|> eos)
     parse_expr
  )
end st
;;

(******************************************************************************)

type env = expr NameMap.t
;;

type lisp_error = AtPos of position * lisp_error
		  | FreeError of string * expr
		  | StringError of string
;;

exception ExecException of lisp_error
;;

let rec eval (e: expr) (ctxt: env ref) : expr =
  match e with
    | SrcInfo (e, pos) -> (
      try
	eval e ctxt
      with
	| ExecException err -> raise (ExecException (AtPos (pos, err)))
	(*| _ -> raise Pervasives.Exit*)
    )    
    | Obj _ as o -> o
    | Int _ as i -> i
    | Float _ as f -> f
    | String _ as s -> s
    | Quoted e -> e
    | Name n -> (
      try 
	NameMap.find n !ctxt
      with
	| Not_found -> raise (ExecException (FreeError ("unknown name", e)))
    )
    | List [] -> List []
    | List ((Obj o)::tl) -> o#apply tl ctxt
    | List (hd::tl) -> 
      let hd' = eval hd ctxt in
      if hd = hd' then
	raise (ExecException (FreeError ("not a function", e)))
      else
	eval (List (hd'::tl)) ctxt
;;

(*********************************)

let rec drop (l: 'a list) (n: int) : 'a list =
  match n with 
    | 0 -> l
    | _ -> drop (List.tl l) (n-1)
;;

let savevals (l: name list) (ctxt: env ref) : (name * expr option) list =
  List.fold_left (fun acc n ->
    try 
      (n, Some (NameMap.find n !ctxt))::acc
    with
      | _ -> (n, None)::acc
  ) [] l
;;

let restorevals (l: (name * expr option) list) (ctxt: env ref) : unit =
  Pervasives.ignore (
    List.map (fun hd -> 
      match hd with
	| (n, None) -> ctxt := NameMap.remove n !ctxt
	| (n, Some e) -> ctxt := NameMap.add n e !ctxt
    ) l
  )
;;

let save_and_restore (l: name list) (ctxt: env ref) (f: unit -> 'a) : 'a =
  let l = savevals l ctxt in
  try 
    let res = f () in
    restorevals l ctxt;
    res
  with
    | e -> restorevals l ctxt; raise e
;;

class lambda (name: string) (doc: string) (listargs: (name * expr option) list) (body: expr list) =
object (self)
  inherit [expr] eObj
  method get_name = name
  method get_doc = doc
  method apply args ctxt =     
  
    let args = args @ List.map (fun (name, value) -> 
      match value with
	| None -> raise (ExecException (StringError "not enough arguments (or missing default value)"))
	| Some value -> eval value ctxt
    ) (drop listargs (List.length args)) in
      
    save_and_restore (fst (List.split listargs)) ctxt (
      fun _ -> 
    
	let args' = List.map (fun e -> eval e ctxt) args in
    
	let _ = List.map (fun ((n, _), v) -> 
	  ctxt := NameMap.add n v !ctxt
	) (List.combine listargs args') in
    
	List.fold_left (fun acc expr -> eval expr ctxt) (List []) body
    )
end;;

let rec extractList (e: expr) : expr list =
  match e with
    | List l -> l
    | SrcInfo (e, pos) -> (
      try extractList e with
	| ExecException err -> raise (ExecException (AtPos (pos, err)))
    )
    | _ -> raise (ExecException (FreeError ("not a list", e)))
;;

let rec extractName (e: expr) : string =
  match e with
    | Name n -> n
    | SrcInfo (e, pos) -> (
      try extractName e with
	| ExecException err -> raise (ExecException (AtPos (pos, err)))
    )
    | _ -> raise (ExecException (FreeError ("not a name", e)))
;;

let rec extractString (e: expr) : string =
  match e with
    | String s -> s
    | SrcInfo (e, pos) -> (
      try extractString e with
	| ExecException err -> raise (ExecException (AtPos (pos, err)))
    )
    | _ -> raise (ExecException (FreeError ("not a string", e)))
;;

class defun =
object (self)
  inherit [expr] eObj
  method get_name = "defun"
  method get_doc = "primitive to define a function\nformat:\n(defun name (params) \"doc\" body"
  method apply args ctxt =     
    if List.length args != 4 then
      raise (ExecException (StringError "wrong number of arguments"))
    else
           
      let listargs = 
	let l = extractList (List.nth args 1) in
	List.map (fun hd -> 
	  try 
	    (extractName hd, None)
	  with
	    | _ -> (
	      try 
		let [argname; defaultvalue] = extractList hd in
		(extractName argname, Some defaultvalue)
	      with
		| _ -> raise (ExecException (FreeError ("wrong argument form", hd)))
	    )
	) l
      in 
      let body = drop args 2 in
      let name = extractName (List.hd args) in
      let doc = extractString (List.nth args 2) in
      let o = Obj (new lambda name doc listargs body) in
      ctxt := NameMap.add name o !ctxt;
      o

end;;

let rec unSrcInfo (e: expr) : expr =
  match e with
    | SrcInfo (e, _) -> unSrcInfo e
    | _ -> e
;;

class plus =
object (self)
  inherit [expr] eObj
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
	| _ -> raise (ExecException (FreeError (String.concat "" ["neither an int or a float ("; exprtype hd; ")"], hd)))
    ) (Int 0) args'
end;;

class mult =
object (self)
  inherit [expr] eObj
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
	| _ -> raise (ExecException (FreeError (String.concat "" ["neither an int or a float ("; exprtype hd; ")"], hd)))
    ) (Int 1) args'
end;;

let rec extractObj (e: expr) : expr eObj =
  match e with
    | Obj o -> o
    | SrcInfo (e, pos) -> (
      try extractObj e with
	| ExecException err -> raise (ExecException (AtPos (pos, err)))
    )
    | _ -> raise (ExecException (FreeError ("not an object", e)))
;;

class getdoc =
object (self)
  inherit [expr] eObj
  method get_name = "getdoc"
  method get_doc = "return the documentation of the function symbol passed as argument"
  method apply args ctxt =     
    if List.length args != 1 then
      raise (ExecException (StringError "wrong number of arguments"))
    else
      let n = extractName (List.nth args 0) in
      let value = try NameMap.find n !ctxt with | Not_found -> raise (ExecException (FreeError ("unknown name", (List.nth args 0)))) in
      let o = extractObj value in
      String o#get_doc
end;;

class elet =
object (self)
  inherit [expr] eObj
  method get_name = "let"
  method get_doc = "lisp let expression\n format: (let varlist body)\n with varlist := ((var0 val0) ... (vari vali))"
  method apply args ctxt =     
  
    if List.length args < 2 then
      raise (ExecException (StringError "not enough arguments for let"))
    else
      let vars = 
	try 
	  let l = extractList (List.nth args 0) in
	  List.map (fun hd ->
	    try 
	      let [var; value] = extractList hd in
	      let n = extractName var in
	      (n, value)
	    with
	      | _ -> 
		let n = extractName hd in
		(n, List [])
	  ) l
	with
	  | _ -> raise (ExecException (FreeError ("this is an improper list of bindings for let", List.nth args 0)))
      in
      
      save_and_restore (fst (List.split vars)) ctxt (
	fun _ -> 
    
	  let _ = List.map (fun (n, value) -> 
	    ctxt := NameMap.add n (eval value ctxt) !ctxt
	  ) vars in    
	  
	  let body = drop args 1 in
	  
	  List.fold_left (fun acc expr -> eval expr ctxt) (List []) body
      )
end;;

class set =
object (self)
  inherit [expr] eObj
  method get_name = "set"
  method get_doc = "set a variable to a value\nformat: (set var value)\nN.B.: both args are evaluated prior to mutation"
  method apply args ctxt =     
    if List.length args != 2 then
      raise (ExecException (StringError "wrong number of arguments"))
    else
      let [var; value] = List.map (fun hd -> eval hd ctxt) args in
      let n = extractName var in
      ctxt := NameMap.add n value !ctxt;
      value      
end;;

class setq =
object (self)
  inherit [expr] eObj
  method get_name = "setq"
  method get_doc = "set a variable to a value\nformat: (set var value)\nN.B.: only value is evaluated prior to mutation"
  method apply args ctxt =     
    if List.length args != 2 then
      raise (ExecException (StringError "wrong number of arguments"))
    else
      let [var; value] = args in
      let value = eval value ctxt in
      let n = extractName var in
      ctxt := NameMap.add n value !ctxt;
      value      
end;;

let rec extractBool (e: expr) : bool =
  match e with
    | SrcInfo (e, pos) -> extractBool e
    | List [] -> false
    | _ -> true
;;

class ifte =
object (self)
  inherit [expr] eObj
  method get_name = "if"
  method get_doc = "conditional branching\nformat (if test then ?else)"
  method apply args ctxt =     
    if List.length args < 2 || List.length args > 3 then
      raise (ExecException (StringError "wrong number of arguments"))
    else
      if extractBool (eval (List.nth args 0) ctxt) then
	eval (List.nth args 1) ctxt else
	if List.length args = 2 then List [] else eval (List.nth args 2) ctxt
end;;

class ewhen =
object (self)
  inherit [expr] eObj
  method get_name = "when"
  method get_doc = "(when COND BODY...)

If COND yields non-nil, do BODY, else return nil.
When COND yields non-nil, eval BODY forms sequentially and return
value of last one, or nil if there are none.
"
  method apply args ctxt =     
    if List.length args < 1 then
      raise (ExecException (StringError "wrong number of arguments"))
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
  method get_name = "t"
  method get_doc = "true value"
  method apply args ctxt = 
    raise (ExecException (StringError "not executable"))
end;;

let exprbool (b: bool) : expr =
  if b then Name "t" else List []
;;

class eEq =
object (self)
  inherit [expr] eObj
  method get_name = "="
  method get_doc = "numerical equality"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (ExecException (StringError "wrong number of arguments"))
     else
       match List.map (fun hd -> eval hd ctxt) args with
	 | [Int i1; Int i2] -> exprbool (i1 = i2)
	 | [Int i1; Float f2] -> exprbool (float i1 = f2)
	 | [Float f1; Int i2] -> exprbool (f1 = float i2)
	 | [Float f1; Float f2] -> exprbool (f1 = f2)
	 | _ -> raise (ExecException (StringError "not numerical arguments"))
end;;

class eGt =
object (self)
  inherit [expr] eObj
  method get_name = ">"
  method get_doc = "numerical Gt"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (ExecException (StringError "wrong number of arguments"))
     else
       match List.map (fun hd -> eval hd ctxt) args with
	 | [Int i1; Int i2] -> exprbool (i1 > i2)
	 | [Int i1; Float f2] -> exprbool (float i1 > f2)
	 | [Float f1; Int i2] -> exprbool (f1 > float i2)
	 | [Float f1; Float f2] -> exprbool (f1 > f2)
	 | _ -> raise (ExecException (StringError "not numerical arguments"))
end;;

class eGe =
object (self)
  inherit [expr] eObj
  method get_name = ">="
  method get_doc = "numerical Ge"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (ExecException (StringError "wrong number of arguments"))
     else
       match List.map (fun hd -> eval hd ctxt) args with
	 | [Int i1; Int i2] -> exprbool (i1 >= i2)
	 | [Int i1; Float f2] -> exprbool (float i1 >= f2)
	 | [Float f1; Int i2] -> exprbool (f1 >= float i2)
	 | [Float f1; Float f2] -> exprbool (f1 >= f2)
	 | _ -> raise (ExecException (StringError "not numerical arguments"))
end;;

class eLt =
object (self)
  inherit [expr] eObj
  method get_name = "<"
  method get_doc = "numerical Lt"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (ExecException (StringError "wrong number of arguments"))
     else
       match List.map (fun hd -> eval hd ctxt) args with
	 | [Int i1; Int i2] -> exprbool (i1 < i2)
	 | [Int i1; Float f2] -> exprbool (float i1 < f2)
	 | [Float f1; Int i2] -> exprbool (f1 < float i2)
	 | [Float f1; Float f2] -> exprbool (f1 < f2)
	 | _ -> raise (ExecException (StringError "not numerical arguments"))
end;;

class eLe =
object (self)
  inherit [expr] eObj
  method get_name = "<="
  method get_doc = "numerical Le"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (ExecException (StringError "wrong number of arguments"))
     else
       match List.map (fun hd -> eval hd ctxt) args with
	 | [Int i1; Int i2] -> exprbool (i1 <= i2)
	 | [Int i1; Float f2] -> exprbool (float i1 <= f2)
	 | [Float f1; Int i2] -> exprbool (f1 <= float i2)
	 | [Float f1; Float f2] -> exprbool (f1 <= f2)
	 | _ -> raise (ExecException (StringError "not numerical arguments"))
end;;

class eeq =
object (self)
  inherit [expr] eObj
  method get_name = "eq"
  method get_doc = "strict equality"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (ExecException (StringError "wrong number of arguments"))
     else
       let [e1; e2] = List.map (fun hd -> eval hd ctxt) args in
       exprbool (eq e1 e2)
end;;

class eequal =
object (self)
  inherit [expr] eObj
  method get_name = "equal"
  method get_doc = "equiv equality"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (ExecException (StringError "wrong number of arguments"))
     else
       let [e1; e2] = List.map (fun hd -> eval hd ctxt) args in
       exprbool (equal e1 e2)
end;;

class estringlt =
object (self)
  inherit [expr] eObj
  method get_name = "string<"
  method get_doc = "string lt"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (ExecException (StringError "wrong number of arguments"))
     else
       let [s1; s2] = List.map (fun hd -> 
	 let hd' = eval hd ctxt in
	 try extractString hd' with | _ -> extractName hd'
       ) args in
       exprbool (s1 < s2)
end;;

class estringlessp =
object (self)
  inherit estringlt
  method get_name = "string-lessp"
end;;

let extractStringOrName (e: expr) : string =
  try extractString e with | _ -> extractName e
;;

class estringeq =
object (self)
  inherit [expr] eObj
  method get_name = "string="
  method get_doc = "string eq"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (ExecException (StringError "wrong number of arguments"))
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
  method get_name = "string-equal"
end;;

let parse_common : string Parser.t =
  matched (?+ (tokenp (function |'\\' | '%' -> false | _ -> true) <?> "common")) >>= fun s -> 
  return s
;;

let rec extractInt (e: expr) : int =
  match e with
    | Int i -> i
    | SrcInfo (e, pos) -> (
      try extractInt e with
	| ExecException err -> raise (ExecException (AtPos (pos, err)))
    )
    | _ -> raise (ExecException (FreeError ("not an int", e)))
;;

let rec extractFloat (e: expr) : float =
  match e with
    | Float f -> f
    | SrcInfo (e, pos) -> (
      try extractFloat e with
	| ExecException err -> raise (ExecException (AtPos (pos, err)))
    )
    | _ -> raise (ExecException (FreeError ("not a float", e)))
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
  return s
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
  method get_name = "message"
  method get_doc = "format a message"
  method apply args ctxt = 
     if List.length args < 1 then
       raise (ExecException (StringError "wrong number of arguments"))
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
	   raise (ExecException (StringError (String.concat "\n" ["in:"; msg; 
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
  method get_name = "print"
  method get_doc = "print an expr"
  method apply args ctxt = 
     if List.length args < 1 then
       raise (ExecException (StringError "wrong number of arguments"))
     else
       let e = eval (List.hd args) ctxt in
       let s = box2string (token2box (expr2token e) 400 2) in
       printf "%s\n" s;
       String s
end;;

class econs =
object (self)
  inherit [expr] eObj
  method get_name = "cons"
  method get_doc = "constructor"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (ExecException (StringError "wrong number of arguments"))
     else
       let [e1; e2] = List.map (fun hd -> eval hd ctxt) args in
       let l = extractList e2 in
       List (e1::l)
end;;

class ecar =
object (self)
  inherit [expr] eObj
  method get_name = "car"
  method get_doc = "extract head of list"
  method apply args ctxt = 
     if List.length args != 1 then
      raise (ExecException (StringError "wrong number of arguments"))
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
  method get_name = "cdr"
  method get_doc = "extract tail of list"
  method apply args ctxt = 
     if List.length args != 1 then
      raise (ExecException (StringError "wrong number of arguments"))
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
  method get_name = "nthcdr"
  method get_doc = "correspond to nth call to cdr"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (ExecException (StringError "wrong number of arguments"))
     else
       let [e1; e2] = List.map (fun hd -> eval hd ctxt) args in
       let l = extractList e2 in
       let n = extractInt e1 in
       if List.length l <= n then List [] else List (drop l n)
end;;

class enth =
object (self)
  inherit [expr] eObj
  method get_name = "nth"
  method get_doc = "returns the nth element of a list"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (ExecException (StringError "wrong number of arguments"))
     else
       let [e1; e2] = List.map (fun hd -> eval hd ctxt) args in
       let l = extractList e2 in
       let n = extractInt e1 in
       if List.length l <= n then List [] else List.nth l n
end;;

class setcar =
object (self)
  inherit [expr] eObj
  method get_name = "setcar"
  method get_doc = "mutate the variable, replacing its head"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (ExecException (StringError "wrong number of arguments"))
     else
       let value = eval (List.nth args 1) ctxt in
       let n = extractName (List.nth args 0) in
       let nvalue = 
	 try 
	   NameMap.find n !ctxt
	 with
	   | Not_found -> raise (ExecException (FreeError ("unknown name", Name n)))
       in 
       let nl = extractList nvalue in
       match nl with
	 | [] -> raise (ExecException (StringError ("the variable has for value nil")))
	 | hd::tl -> let nvalue = List (value::tl) in
		     ctxt := NameMap.add n nvalue !ctxt;
		     value

end;;

class setcdr =
object (self)
  inherit [expr] eObj
  method get_name = "setcdr"
  method get_doc = "mutate the variable, replacing its tail"
  method apply args ctxt = 
     if List.length args != 2 then
      raise (ExecException (StringError "wrong number of arguments"))
     else
       let value = extractList (eval (List.nth args 1) ctxt) in
       let n = extractName (List.nth args 0) in
       let nvalue = 
	 try 
	   NameMap.find n !ctxt
	 with
	   | Not_found -> raise (ExecException (FreeError ("unknown name", Name n)))
       in 
       let nl = extractList nvalue in
       match nl with
	 | [] -> raise (ExecException (StringError ("the variable has for value nil")))
	 | hd::tl -> let nvalue = List (hd::value) in
		     ctxt := NameMap.add n nvalue !ctxt;
		     List value

end;;

class length =
object (self)
  inherit [expr] eObj
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
      raise (ExecException (StringError "wrong number of arguments"))
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
  method get_name = "symbol-name"
  method get_doc = "(symbol-name SYMBOL)

Return SYMBOL's name, a string.
"
  method apply args ctxt = 
     if List.length args != 1 then
      raise (ExecException (StringError "wrong number of arguments"))
     else
       String (extractName (eval (List.hd args) ctxt))
end;;


class enot =
object (self)
  inherit [expr] eObj
  method get_name = "not"
  method get_doc = "negation"
  method apply args ctxt = 
     if List.length args != 1 then
      raise (ExecException (StringError "wrong number of arguments"))
     else
       exprbool (not (extractBool (eval (List.nth args 0) ctxt)))
end;;

class ewhile =
object (self)
  inherit [expr] eObj
  method get_name = "while"
  method get_doc = "while loop\nformat: (while test body...)"
  method apply args ctxt = 
     if List.length args < 1 then
      raise (ExecException (StringError "wrong number of arguments"))
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
  method get_name = "dolist"
  method get_doc = "(dolist (VAR LIST [RESULT]) BODY...)\nLoop over a list.\nEvaluate BODY with VAR bound to each car from LIST, in turn.\nThen evaluate RESULT to get return value, default nil.\n"
  method apply args ctxt = 
     if List.length args < 2 then
      raise (ExecException (StringError "wrong number of arguments"))
     else
       let param = List.hd args in
       let body = List.tl args in
       let [var; list; result] = extractList param in
       let var = extractName var in
       let list = extractList (eval list ctxt) in
       let result = extractName result in
       
       save_and_restore [var] ctxt (
	 fun _ -> 

	   let _ = List.fold_left (fun acc hd -> 
	     ctxt := NameMap.add var hd !ctxt;
	     Pervasives.ignore(List.fold_left (fun acc hd -> Pervasives.ignore(eval hd ctxt)) () body)
	   ) () list in
	   try NameMap.find result !ctxt with _ -> List []
       )
end;;

let rec from_to (from: int) (ito: int) : int list =
  if from > ito then [] else from::(from_to (from+1) ito)
;;

class dotimes =
object (self)
  inherit [expr] eObj
  method get_name = "dotimes"
  method get_doc = "
(dotimes (VAR COUNT [RESULT]) BODY...)

Loop a certain number of times.
Evaluate BODY with VAR bound to successive integers running from 0,
inclusive, to COUNT, exclusive.  Then evaluate RESULT to get
the return value (nil if RESULT is omitted)."
  method apply args ctxt = 
     if List.length args < 2 then
      raise (ExecException (StringError "wrong number of arguments"))
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
	     ctxt := NameMap.add var (Int hd) !ctxt;
	     Pervasives.ignore(List.fold_left (fun acc hd -> Pervasives.ignore(eval hd ctxt)) () body)
	   ) () (from_to 0 count) in
	   try NameMap.find result !ctxt with _ -> List []
       )
end;;

class plusone =
object (self)
  inherit [expr] eObj
  method get_name = "1+"
  method get_doc = "(1+ NUMBER)

Return NUMBER plus one.  NUMBER may be a number or a marker.
Markers are converted to integers."
  method apply args ctxt = 
     if List.length args != 1 then
      raise (ExecException (StringError "wrong number of arguments"))
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
	     | _ -> raise (ExecException (FreeError ("not a numerical", List.nth args 0)))

end;;

class minusone =
object (self)
  inherit [expr] eObj
  method get_name = "1-"
  method get_doc = "(1- NUMBER)

Return NUMBER minus one.  NUMBER may be a number or a marker.
Markers are converted to integers."
  method apply args ctxt = 
     if List.length args != 1 then
      raise (ExecException (StringError "wrong number of arguments"))
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
	     | _ -> raise (ExecException (FreeError ("not a numerical", List.nth args 0)))

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
  method get_name = "current-time-string"
  method get_doc = "simple version without args"
  method apply args ctxt = 
     if List.length args != 0 then
      raise (ExecException (StringError "wrong number of arguments"))
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
  method get_name = "list"
  method get_doc = "returns its args in a list"
  method apply args ctxt = 
    List (List.map (fun hd -> eval hd ctxt) args)
end;;


(******************************************************************************)

let ctxt : env ref = ref NameMap.empty;;

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
		 ];;

let _ = 
  List.fold_left (fun acc o -> 
    ctxt := NameMap.add o#get_name (Obj o) !ctxt
  ) () primitives


let rec execException2box (e: lisp_error) : token =
  match e with
    | StringError s -> Verbatim s
    | FreeError (s, e) -> Box [Verbatim s; Verbatim ":"; Space 1; Verbatim "'"; expr2token e; Verbatim "'"; ]
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

let interp_expr expr = 
  (*printf "term = '%s'\n" s;*)
  let stream = Stream.from_string ~filename:"stdin" expr in
  match parse_expr stream with
    | Result.Ok (res, _) -> (
      (*
      printf "pprint = "; 
      printbox (token2box (expr2token res) 400 2);
      *)
      try (
	let res' = eval res ctxt in
	printbox (token2box (expr2token res') 400 2);
	res'
      )
      with
	| ExecException e -> printbox (token2box (execException2box e) 400 2); List []
    )
    | Result.Error (pos, s) ->
      Format.eprintf "%s\n%a: syntax error: %s@." expr Position.File.format pos s;      
      raise Pervasives.Exit
;;

let interp_exprs expr = 
  (*printf "term = '%s'\n" s;*)
  let stream = Stream.from_string ~filename:"stdin" expr in
  match parse_exprs stream with
    | Result.Ok (res, _) -> (
      (*
       let _ = List.map (fun hd -> 
	printf "pprint = "; 
	printbox (token2box (expr2token hd) 400 2);
      ) res in
      *)
      try (
	let res' = List.fold_left (fun acc hd -> eval hd ctxt) (List []) res in
	printbox (token2box (expr2token res') 400 2);
	res'
      )
      with
	| ExecException e -> printbox (token2box (execException2box e) 400 2); List []
    )
    | Result.Error (pos, s) ->
      Format.eprintf "%s\n%a: syntax error: %s@." expr Position.File.format pos s;      
      raise Pervasives.Exit
;;

(******************************************************************************)


let _ = interp_expr "(+ 2.3 5 6 2.1)";;

let _ = interp_expr "
; this is a function
(defun add1 ((a 0)) ; this is a comment
 \"la doc\"         
 (+ a 1)   
)
";;

let _ = interp_expr "(add1 8)";;

let _ = interp_expr "(add1)";;

let _ = interp_expr "(getdoc add1)";;

let _ = interp_expr "(setq x 0)";;

let _ = interp_expr "(set 'y 0)";;

let _ = interp_expr "(let ((x 2) (y 2)) (+ x y))";;

let _ = interp_expr "x";;

let _ = interp_expr "y";;

let _ = interp_expr "(if () 'true 'false)"

let _ = interp_expr "(if t 'true 'false)"

let _ = interp_expr "(= 1 1.0)"

let _ = interp_expr "(< 1 1.0)"

let _ = interp_expr "(eq t t)"

let _ = interp_expr "(string= \"aa\" \"aa\")"

let _ = interp_expr "(string< \"aa\" \"aa\")"

let _ = interp_expr "(message \"salut doudou %s %d times !!!!!!\" 'nicolas 3.23)"

let _ = interp_expr "(cons 'doudou '(rou))"

let _ = interp_expr "(car '(doudou rou)))"

let _ = interp_expr "(cdr '(doudou rou)))"

let _ = interp_expr "(nthcdr 3 '(asd asd asd asd asd ou rou)))"

let _ = interp_expr "(nth 3 '(asd asd asd asd asd ou rou)))"

let _ = interp_exprs "
(setq x '(rou dou dou))

(setcar x 'prout)

x

(setcdr x '(rpout prout))

x
"
;;

let _ = interp_exprs "
(setq animals '(gazelle giraffe lion tiger))
     
(defun print-elements-of-list (list)
       \"Print each element of LIST on a line of its own.\"
       (while list
         (message \"%s\n\" (car list))
         (setq list (cdr list))))

(print-elements-of-list animals)

"
;;

let _ = interp_exprs "
(setq animals '(gazelle giraffe lion tiger))
     
(defun reverse-list-with-dolist (list)
    \"Using dolist, reverse the order of LIST.\"
    (let (value)  ; make sure list starts empty
      (dolist (element list value)
      (setq value (cons element value)))))
     
(reverse-list-with-dolist animals)
";;

let _ = interp_exprs "
(let (value)      ; otherwise a value is a void variable
       (dotimes (number 3 value)
         (setq value (cons number value))))
";;

let _ = interp_exprs "
(defun triangle-using-dotimes (number-of-rows)
   \"Using dotimes, add up the number of pebbles in a triangle.\"
     (let ((total 0))
       (dotimes (number number-of-rows total)
         (setq total (+ total (1+ number))))))
     
     (triangle-using-dotimes 4)
";;

let _ = interp_exprs "
(setq animals '(gazelle giraffe lion tiger))
     
     (defun print-elements-recursively (list)
       \"Print each element of LIST on a line of its own.
     Uses recursion.\"
       (when list                            ; do-again-test
             (print (car list))              ; body
             (print-elements-recursively     ; recursive call
              (cdr list))))                  ; next-step-expression
     
     (print-elements-recursively animals)
";;

let _ = interp_exprs "
(defun triangle-recursively (number)
       \"Return the sum of the numbers 1 through NUMBER inclusive.
     Uses recursion.\"
       (if (= number 1)                    ; do-again-test
           1                               ; then-part
         (+ number                         ; else-part
            (triangle-recursively          ; recursive call
             (1- number)))))               ; next-step-expression
     
     (triangle-recursively 7)
";;

let _ = interp_exprs "
(defun square-each (numbers-list)
       \"Square each of a NUMBERS LIST, recursively.\"
       (if (not numbers-list)                ; do-again-test
           nil
         (cons
          (* (car numbers-list) (car numbers-list))
          (square-each (cdr numbers-list))))) ; next-step-expression
     
     (square-each '(1 2 3))
";;


let _ = interp_exprs "
(setq animals '(gazelle giraffe lion tiger))
     
     (defun print-elements-recursively (list)
       \"Print each element of LIST on a line of its own.
     Uses recursion.\"
       (when list                            ; do-again-test
             (print (car list))              ; body
             (print-elements-recursively     ; recursive call
              (cdr list))))                  ; next-step-expression
     
     (print-elements-recursively animals)
"
;;


let _ = interp_exprs "
(defun add-elements (numbers-list)
       \"Add the elements of NUMBERS-LIST together.\"
       (if (not numbers-list)
           0
         (+ (car numbers-list) (add-elements (cdr numbers-list)))))
     
     (add-elements '(1 2 3 4))
";;

let _ = interp_exprs "
(defun keep-three-letter-words (word-list)
       \"Keep three letter words in WORD-LIST.\"
       (cond
        ;; First do-again-test: stop-condition
        ((not word-list) nil)
     
        ;; Second do-again-test: when to act
        ((eq 3 (length (symbol-name (car word-list))))
         ;; combine acted-on element with recursive call on shorter list
         (cons (car word-list) (keep-three-letter-words (cdr word-list))))
     
        ;; Third do-again-test: when to skip element;
        ;;   recursively call shorter list with next-step expression
        (t (keep-three-letter-words (cdr word-list)))))
     
     (keep-three-letter-words '(one two three four five six))
";;

let _ = interp_exprs "
(defun triangle-initialization (number)
       \"Return the sum of the numbers 1 through NUMBER inclusive.
     This is the `initialization' component of a two function
     duo that uses recursion.\"
       (triangle-recursive-helper 0 0 number))
     (defun triangle-recursive-helper (sum counter number)
       \"Return SUM, using COUNTER, through NUMBER inclusive.
     This is the `helper' component of a two function duo
     that uses recursion.\"
       (if (> counter number)
           sum
         (triangle-recursive-helper (+ sum counter)  ; sum
                                    (1+ counter)     ; counter
                                    number)))        ; number
(triangle-initialization 2)
";;

let _ = interp_exprs "
(defun silly-loop (n)
       \"Return time before and after N iterations of a loop.\"
       (let ((t1 (current-time-string)))
         (while (> (setq n (1- n))
                   0))
         (list t1 (current-time-string))))

(silly-loop 1000)
";;




