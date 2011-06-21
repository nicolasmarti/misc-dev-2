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

let e1 = List [Obj (new plus); Int 8; Float 3.1; Float 1.]
;;

let empty_ctxt = ref NameMap.empty
;;

open Printf;;

printf "%s --> %s\n" (expr2string e1) (expr2string (eval e1 empty_ctxt))
;;
