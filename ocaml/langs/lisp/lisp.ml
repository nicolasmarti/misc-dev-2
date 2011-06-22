(*

ocamlfind ocamlopt -package spotlib,planck -c lisp.ml
ocamlfind ocamlopt -package spotlib,planck -o test lisp.cmx -linkpkg

*)

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

(******************************************************************************)

let rec expr2string (e: expr) : string =
  match e with
    | Obj o -> o#get_name
    | Int i -> string_of_int i
    | Float f -> string_of_float f
    | String s -> String.concat "" ["\""; s; "\""]
    | Name n -> n
    | Quoted e -> String.concat "" ["'"; expr2string e]
    | List l -> String.concat "" ["("; String.concat " " (List.map expr2string l); ")"]
    | SrcInfo (e, _) -> expr2string e
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

let constant_int st = begin
  (* [0-9]+ *)
  (matched (?+ (tokenp (function '0'..'9' -> true | _ -> false) <?> "decimal")) >>= fun s -> 
   return (int_of_string s))
end st

let constant_float st = begin
  (* [0-9]+[.][0-9]+ *)
  (matched (?+ (tokenp (function '0'..'9' -> true | _ -> false) <?> "float")) >>= fun s1 -> 
   token '.' >>= fun _ ->
   matched (?+ (tokenp (function '0'..'9' -> true | _ -> false) <?> "float")) >>= fun s2 -> 
   return (float_of_string (String.concat "." [s1; s2])))
end st

let parse_name st = begin
    (matched (?+ (tokenp (function 'a'..'z' -> true | 'A'..'Z' -> true | _ -> false) <?> "var")) >>= fun s -> 
     return s
    )    
end st

let parse_symbol st = begin
    (matched (?+ (tokenp (fun x ->  
      List.mem x ['+'; '-'; '*']
     ) <?> "symbol"
     )
     ) >>= fun s -> 
     return s
    )    
end st

let blank = ignore (one_of [' '; '\t'; '\n'; '\r'])

let rec parse_expr st = begin
  withPos (
    try_ (constant_float >>= fun i -> return (Float i))
    <|> try_ (constant_int >>= fun i -> return (Int i))
    <|> try_ (parse_symbol >>= fun s -> return (Name s))
    <|> try_ (parse_name >>= fun s -> return (Name s))
    <|> try_ (token '\'' >>= fun _ -> parse_expr >>= fun e -> return (Quoted e))
    <|> (surrounded (token '(') (token ')') (list_with_sep ~sep:(?+ blank) parse_expr) >>= fun l -> return (List l))
  ) >>= fun (e, startp, endp) ->
  return (SrcInfo (e, (startp, endp)))
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
	| _ -> raise Pervasives.Exit
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

(* this first version does not take account for default val of parameters*)
class lambda (name: string) (listargs: (name * expr option) list) (body: expr list) =
object (self)
  inherit [expr] eObj
  method get_name = name
  method apply args ctxt =     
    if List.length args != List.length listargs then
      raise (ExecException (StringError "wrong number of arguments"))
    else
      
      let oldvals = List.fold_right (fun (n, _) acc ->
	try 
	  (n, NameMap.find n !ctxt)::acc
	with
	  | Not_found -> acc
      ) listargs [] in

      let args' = List.map (fun e -> eval e ctxt) args in
      
      let _ = List.map (fun ((n, _), v) -> 
	  ctxt := NameMap.add n v !ctxt
	) (List.combine listargs args') in
      
      let res = List.fold_left (fun acc expr -> eval expr ctxt) (List []) body in

      let _ = List.map (fun (n, v) -> 
	ctxt := NameMap.add n v !ctxt
      ) oldvals in

      res
end;;

(* this first version does not take account for default val of parameters*)
class plus =
object (self)
  inherit [expr] eObj
  method get_name = "+"
  method apply args ctxt =     
    let args' = List.map (fun e -> eval e ctxt) args in
    List.fold_left (fun acc hd ->
      match acc, hd with
	| (Int sum, Int a) -> Int (sum + a)
	| (Int sum, Float a) -> Float (float sum +. a)
	| (Float sum, Int a) -> Float (sum +. float a)
	| (Float sum, Float a) -> Float (sum +. a)
	| _ -> raise (ExecException (FreeError ("neither an int or a float", hd)))
    ) (Int 0) args'
end;;

(******************************************************************************)

let ctxt : env ref = ref NameMap.empty;;

let primitives = [(new plus)];;

let _ = 
  List.fold_left (fun acc o -> 
    ctxt := NameMap.add o#get_name (Obj o) !ctxt
  ) () primitives


open Printf;;

let rec execException2box (e: lisp_error) : token =
  match e with
    | StringError s -> Verbatim s
    | FreeError (s, e) -> Box [Verbatim s; Verbatim ":"; Space 1; expr2token e]
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
					execException2box e;
				       ]
;;

let interp s = 
  (*printf "term = '%s'\n" s;*)
  let stream = Stream.from_string ~filename:"stdin" s in
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
      Format.eprintf "%a: syntax error: %s@." Position.File.format pos s;      
      List []
;;


let e1 = "(+ 2.3 5 6 2.1)"
;;

interp e1;;