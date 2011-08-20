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

  Copyright (C) 2008 Nicolas Marti
*)

open List;;
open String;;
open Varset;;
open Def;;
open Freshness;;
open Arith;;
open Def;;
open Unfold;;
open Printer;;
open Printf;;
open Varmap;;
open Term;;

let rec term_size_arith t def =
  match t with      
    | Var v -> 
        Some (Nvar v)

    | App (t1, t2) -> (

        let l = t1::t2 in

	  List.fold_left (

	    fun tl hd ->

	      match tl with
		| None -> None
		| Some n ->
		    match (term_size_arith hd def) with
		      | None -> None
		      | Some n' -> Some (Nplus (n, n'))

	  ) (Some (Ncons 0)) l	    

      )

    | Cons (n, _) -> Some (Ncons 1)

    | Type -> Some (Ncons 1)

    | Cste c -> (
	
	let te = unfold_cste c def in
	  if (te = Cste c) then
	    None
	  else
	    term_size_arith te def

      )

    | Obj o -> Some (Ncons 1)

    | Lambda (x, t1, t2) -> ( 
	match (term_size_arith t1 def, term_size_arith t2 def) with
	  | (Some s1, Some s2) ->
	      Some (Nplus (s1, s2))
	  | _ -> None
      )


    | Forall (x, t1, t2) -> ( 
	match (term_size_arith t1 def, term_size_arith t2 def) with
	  | (Some s1, Some s2) ->
	      Some (Nplus (s1, s2))
	  | _ -> None
      )

    | Ind (x, la, ty, lcons) -> (
	
	let te = (largs_foralls ty la) in
	  match (term_size_arith te def, sum_term_size_arith lcons def) with
	    | (Some s1, Some s2) ->
		Some (Nplus (s1, s2))
	    | _ -> None
	    
      )

    | _ -> 
	(*printf "term_size_arith, not supported:= %s\n\n" (string_of_term t VarMap.empty); *)
	  None
and sum_term_size_arith l def =
  List.fold_left (
    
    fun tl hd ->
      
      match tl with
	| None -> None
	| Some n ->
	    match (term_size_arith hd def) with
	      | None -> None
	      | Some n' -> Some (Nplus (n, n'))
		  
  ) (Some (Ncons 0)) l	    
;;
  
let list_term_size_arith_gt0 l def =
  List.fold_left (
    
    fun tl hd ->
      
      match (term_size_arith hd def) with
	| None -> tl
	| Some n -> Band (tl, (Bgt (n, Ncons 0)))
		  
  ) BTrue l	    

;;
    
