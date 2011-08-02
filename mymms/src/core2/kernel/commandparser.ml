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
open Ast;;
open Astparser;;


(* helper *)

let args (p: 'a pparser) = 
  (tryrule (fun pb ->		
	      let _ = keyword "(" () pb in
	      let t1 = named_parser "var" p pb in		 
	      let _ = keyword ":" () pb in
	      let t2 = named_parser "ast" p pb in		 
	      let _ = keyword ")" () pb in
		(Explicite, t1, t2)
	   )
  ) 
  <|> (tryrule (fun pb ->		
		  let _ = keyword "{" () pb in
		  let t1 = named_parser "var" p pb in		 
		  let _ = keyword ":" () pb in
		  let t2 = named_parser "ast" p pb in		 
		  let _ = keyword "}" () pb in
		    (Hidden, t1, t2)
	       )
      ) 
    <|> (tryrule (fun pb ->		
		    let _ = keyword "[" () pb in
		    let t1 = named_parser "var" p pb in		 
		    let _ = keyword ":" () pb in
		    let t2 = named_parser "ast" p pb in		 
		    let _ = keyword "]" () pb in
		      (Implicite, t1, t2)
		 )
	) 
;;

let constructor (p: 'a pparser) = 
  (tryrule (fun pb ->		
	      let _ = keyword "|" () pb in
	      let t1 = named_parser "var" p pb in		 
	      let _ = keyword ":" () pb in
	      let t2 = named_parser "ast" p pb in		 
		(t1, t2)
	   )
  ) 
;;

type command =
  | Definition of string * ast * ast option
  | Recursive of string * ast * ast option
  | Inductive of string * ast * ast option
  | Expression of ast
;;

(* Inductive parser *)

let inductive_parser =
    (
      fun pb ->
	((tryrule (fun pb ->
		     let _ = keyword "Inductive" () pb in
		     let x = named_parser "var" astpparser pb in
		     let args = many (args astpparser) pb in
		     let _ = keyword ":" () pb in
		     let ty = named_parser "ast" astpparser pb in
		     let _ = keyword ":=" () pb in
		     let constructor = many (constructor astpparser) pb in
		     let _ = keyword "." () pb in
		     let constructor' = List.map (fun (hd1, hd2) ->
						    match hd1 with
						      | Symb (_, v) -> (v, hd2)
						      | _ -> raise NoMatch
						 ) constructor in
		     let args' = List.map (fun (n, hd1, hd2) ->
					     match hd1 with
					       | Symb (_, v) -> (n, v, hd2)
					       | _ -> raise NoMatch
					  ) args in
		       match x with
			 | Symb (_, x) -> Inductive (x, Ind (x, args', ty, constructor'), None)
			 | _ -> raise NoMatch
			     
		  )
	 )
	 <|> (tryrule (fun pb ->
		     let _ = keyword "Inductive" () pb in
		     let x = named_parser "var" astpparser pb in
		     let args = many (args astpparser) pb in
		     let _ = keyword ":=" () pb in
		     let constructor = many (constructor astpparser) pb in
		     let _ = keyword "." () pb in
		     let constructor' = List.map (fun (hd1, hd2) ->
						    match hd1 with
						      | Symb (_, v) -> (v, hd2)
						      | _ -> raise NoMatch
						 ) constructor in
		     let args' = List.map (fun (n, hd1, hd2) ->
					     match hd1 with
					       | Symb (_, v) -> (n, v, hd2)
					       | _ -> raise NoMatch
					  ) args in
		       match x with
			 | Symb (_, x) -> Inductive (x, Ind (x, args', Avar, constructor'), None)
			 | _ -> raise NoMatch
			     
		  )
	 )
	) pb
    );;

(* Recursive parser *)

let recursive_parser =
  (
    fun pb ->
      (
	(tryrule (fun pb ->
		    let _ = keyword "Recursive" () pb in
		    let x = named_parser "var" astpparser pb in
		    let args = many (args astpparser) pb in
		    let _ = keyword ":" () pb in
		    let ty = named_parser "ast" astpparser pb in
		    let _ = keyword ":=" () pb in
		    let body = named_parser "ast" astpparser pb in
		    let _ = keyword "." () pb in
		    let args' = List.map (fun (n, hd1, hd2) ->
					    match hd1 with
					      | Symb (_, v) -> (n, v, hd2)
					      | _ -> raise NoMatch
					 ) args in
		      match x with
			| Symb (_, x) -> Recursive (x, Phi (x, args', ty, Nothing, body), 
						    None
						   )
			| _ -> raise NoMatch			   
		 )
	)
	<|> (tryrule (fun pb ->
		    let _ = keyword "Recursive" () pb in
		    let x = named_parser "var" astpparser pb in
		    let args = many (args astpparser) pb in
		    let _ = keyword ":=" () pb in
		    let body = named_parser "ast" astpparser pb in
		    let _ = keyword "." () pb in
		    let args' = List.map (fun (n, hd1, hd2) ->
					    match hd1 with
					      | Symb (_, v) -> (n, v, hd2)
					      | _ -> raise NoMatch
					 ) args in
		      match x with
			| Symb (_, x) -> Recursive (x, Phi (x, args', Avar, Nothing, body), None)
			| _ -> raise NoMatch			   
		 )
	)
      ) pb
  )
;;

(* Definition parser *)

let definition_parser =
  (
    fun pb ->
      (
	(tryrule (fun pb ->
		    let _ = keyword "Definition" () pb in
		    let x = named_parser "var" astpparser pb in
		    let args = many (args astpparser) pb in
		    let _ = keyword ":" () pb in
		    let ty = named_parser "ast" astpparser pb in
		    let _ = keyword ":=" () pb in
		    let body = named_parser "ast" astpparser pb in
		    let _ = keyword "." () pb in
		    let args' = List.map (fun (n, hd1, hd2) ->
					    match hd1 with
					      | Symb (_, v) -> (n, v, hd2)
					      | _ -> raise NoMatch
					 ) args in
		    let te = List.fold_right (fun (n, x, ty) acc -> Lambda (n, x, ty, acc)) args' body in
		    let ty = List.fold_right (fun (n, x, ty) acc -> Forall (n, x, ty, acc)) args' ty in
		      match x with
			| Symb (_, x) -> Definition (x, te, Some ty)
			| _ -> raise NoMatch			   
		 )
	)
	<|> (tryrule (fun pb ->
		    let _ = keyword "Definition" () pb in
		    let x = named_parser "var" astpparser pb in
		    let args = many (args astpparser) pb in
		    let _ = keyword ":=" () pb in
		    let body = named_parser "ast" astpparser pb in
		    let _ = keyword "." () pb in
		    let args' = List.map (fun (n, hd1, hd2) ->
					    match hd1 with
					      | Symb (_, v) -> (n, v, hd2)
					      | _ -> raise NoMatch
					 ) args in
		    let te = List.fold_right (fun (n, x, ty) acc -> Lambda (n, x, ty, acc)) args' body in
		      match x with
			| Symb (_, x) -> Definition (x, te, None)
			| _ -> raise NoMatch			   
		 )
	)
      ) pb
  )
;;

(* an expression *)
let expr_parser =
  fun pb ->
    let body = named_parser "ast" astpparser pb in
    let _ = keyword "." () pb in
      Expression body
;;


let commandparser = 
  fun pb ->
    (tryrule inductive_parser 
     <|> tryrule recursive_parser 
       <|> tryrule definition_parser
	 <|> tryrule expr_parser
    ) pb
;;
