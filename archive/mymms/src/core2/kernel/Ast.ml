(*
  This file is part of Mymms.

  Mymms is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  Mymms is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with Mymms.  If not, see <http://www.gnu.org/licenses/>.

  Copyright (C) Nicolas Marti
*)

open Str;;
open Pparser;;
open Pprinter;;
open Listext;;
open Varmap;;
open Varset;;
open Printf;;

(* symbol is just a string *)
type symb = string;;

type nature =
  | Implicite
  | Explicite
  | Hidden
;;

type terminaison_pattern =
    Nothing
;;


type ast =
    
  (* the basic type Type *)
  | Type

  (* a symbol could refer to a var or a cste *)
  (* the bool is for unification for ppretty *)
  (* not to be considered in termchecking *)
  | Symb of bool * symb

  (* basic quantification *)
  | Let of symb * ast * ast
  | Lambda of nature * symb * ast * ast
  | Forall of nature * symb * ast * ast

  (* Application *)
  | App of ast list

  (* Destructor *)
  | Match of ast * (ast * ast) list * ast option

  (* Anonymous variable , _*)
  | Avar

  (* maybe should add ind, phi and cons *)

  | Phi of (symb * (nature * symb * ast) list * ast * terminaison_pattern * ast)
  | Ind of (symb * (nature * symb * ast) list * ast * (string * ast) list)
  | Constr of (int * ast)

;;

let rec flattenastapp (a: ast) : ast =
  match a with 
    | App l -> (
	
	match l with
	  | [] -> raise (Failure "flattenastapp: empty list of applications")
	  | hd::[] -> flattenastapp hd
	  | hd::tl ->
	      match flattenastapp hd with
		| App l' -> App (l' @ l)
		| hd' -> App (hd'::tl)
      )
    | _ -> a


(* for debug *)

let rec ast2token (t: ast) : token list =
match t with
    | Type -> (Verbatim "Type") :: []
    | Symb (true, s) -> (Verbatim (String.concat "" ("[" :: s :: "]" :: []))) :: []
    | Symb (false, s) -> (Verbatim (String.concat "" ("[@" :: s :: "]" :: []))) :: []
    | App l -> (Verbatim "<") :: (concatenate (Space 1) (List.map (fun hd -> 
								     match hd with
								       | App l2 ->
									   if List.length l2 > 1 then
									     (Verbatim "(") :: (Box (ast2token hd)) :: (Verbatim ")") :: []
									   else
									     (Box (ast2token hd)) :: []
								       | _ -> (Box (ast2token hd)) :: []
								  )				    
							   l
							)
				 ) @ (Verbatim ">") :: []	
    | Let (v, t1, t2) -> 
	let t1 = Box (ast2token t1) in
	let t2 = Box (ast2token t2) in
	  ((Verbatim "let") :: (Space 1) :: (Verbatim v) :: (Space 1) :: (Verbatim "=") :: (Space 1) :: t1 :: (Space 1) :: (Verbatim "in") :: (Space 1) :: t2 :: [])
    | Lambda (n, v, t1, t2) -> (
	let t1 = Box (ast2token t1) in
	let t2 = Box (ast2token t2) in
	let (a, b) = 
	  match n with
	    | Implicite -> (Verbatim "[", (Verbatim "] ->"))
	    | Explicite -> (Verbatim "(", (Verbatim ") ->"))
	    | Hidden -> (Verbatim "{", (Verbatim "} ->"))
	in
	  ((Verbatim "\\") :: (Space 1) :: a :: (Verbatim v) :: (Verbatim ":") :: t1 :: b :: (Space 1) :: t2 :: [])
      )
    | Forall (n, v, t1, t2) -> (
	let t1 = Box (ast2token t1) in
	let t2 = Box (ast2token t2) in
	let (a, b) = 
	  match n with
	    | Implicite -> (Verbatim "[", (Verbatim "]."))
	    | Explicite -> (Verbatim "(", (Verbatim ")."))
	    | Hidden -> (Verbatim "{", (Verbatim "}."))
	in
	  ((Verbatim "V") :: (Space 1) :: a :: (Verbatim v) :: (Verbatim ":") :: t1 :: b :: (Space 1) :: t2 :: [])
      )
    | Avar -> (Verbatim "_") :: []
    | Match (t1, t2, t3) ->
	let t1 = Box (ast2token t1) in
	let t2 = List.concat (List.map (fun hd -> 
					  let hd1 = Box (ast2token (fst hd)) in
					  let hd2 = Box (ast2token (snd hd)) in
					    (Space 2) :: (Verbatim "|") :: (Space 1) :: hd1 :: (Space 1) :: (Verbatim "==>") :: (Space 1) :: hd2 :: Newline :: []
				       ) t2) in
	let t3 = (match t3 with
		    | None ->  []
		    | Some t3 -> (Space 1) :: (Verbatim "returns") :: (Space 1) :: Box (ast2token t3) :: []
		 ) in
	  (Verbatim "match") :: (Space 1) :: t1 :: t3 @ (Space 1) :: (Verbatim "with") :: Newline :: t2 
    | Phi (x, largs, ty, term, body) -> raise (Failure "ast2token: case not supported (Phi)")
    | Ind (x, largs, ty, lcons) -> raise (Failure "ast2token: case not supported (Ind)")
    | Constr (x, ity) -> raise (Failure "ast2token: case not supported (Cons)")
;;
  
let pprint2ast a =
  let t = ast2token a in
  let t = Box t in
  let b = token2box t 80 2 in
    printbox b
;;


(* function that returns the vars of a destructor pattern *)
let rec destructor_pattern_var (a: ast) : VarSet.t =
  match a with
    | Type -> VarSet.empty
    | Constr (_, _) -> VarSet.empty
    | Symb (_, s) -> VarSet.singleton s
    | App l -> List.fold_left (fun acc hd -> acc +++ (destructor_pattern_var hd)) VarSet.empty l
    | Avar -> VarSet.empty
    | _ -> raise (Failure "destructor_pattern_var: Not a proper term for destruction pattern")
;;

(* function that returns the vars of a destructor body 
   TODO!!!
*)
let rec destructor_body_var (a: ast) : VarSet.t =
  match a with
    | Type -> VarSet.empty
    | Constr (_, _) -> VarSet.empty
    | Symb (_, s) -> VarSet.singleton s
    | App l -> List.fold_left (fun acc hd -> acc +++ (destructor_body_var hd)) VarSet.empty l
    | Avar -> VarSet.empty
    | _ -> raise (Failure "destructor_body_var: case not supported")
;;

let rec rewriteast (a: ast) subs : ast =
  match a with
    | Type -> Type
    | Symb (n, s) -> (
	try 
	  let t' = VarMap.find s subs in
	    t'
	with
	  | Not_found -> Symb (n, s)
      )
    | App l -> 
	App (List.map (fun hd -> rewriteast hd subs) l)
    | Let (v, t1, t2) -> 
	Let (v, rewriteast t1 subs, rewriteast t2 (VarMap.remove v subs))
    | Lambda (n, v, t1, t2) -> 
	Lambda (n, v, rewriteast t1 subs, rewriteast t2 (VarMap.remove v subs))
    | Forall (n, v, t1, t2) -> 
	Forall (n, v, rewriteast t1 subs, rewriteast t2 (VarMap.remove v subs))
    | Avar -> Avar
    | Match (t1, t2, t3) -> 
	Match (rewriteast t1 subs, 
	       List.map (fun hd -> 
			   (fst hd, rewriteast (snd hd) (List.fold_left (fun acc hd -> VarMap.remove hd acc) subs (VarSet.elements (destructor_pattern_var (fst hd)))))
			) t2, 
	       match t3 with
		 | None -> None
		 | Some t3 -> Some (rewriteast t3 subs)
	      )
	
    | Phi (x, largs, ty, term, body) -> raise (Failure "rewriteast: case not supported (Phi)")
    | Ind (x, largs, ty, lcons) -> raise (Failure "rewriteast: case not supported (Ind)")
    | Constr (n, ity) -> raise (Failure "rewriteast: case not supported (Cons)")
;;
