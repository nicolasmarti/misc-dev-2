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

open Def;;
open Printer;;
open Varset;;
open Varmap;;
open Printf;;
open Termeq;;
open Term;;
open Definition;;
open Unification;;
open Listext;;
open List;;

(* FIXME: to primitive *)

let rec get_in_ctxt ctxt ty def =

  (*printf "TypeClass oracle, looking for %s in %s\n\n" (string_of_term ty VarMap.empty) (string_of_listvarterm ctxt VarMap.empty);*)
  
  List.fold_left (
    
    fun acc hd ->
      
      match acc with
	| None -> (
	    
	    let (v, m_ty) = hd in
	      
	      if (term_eq m_ty ty def) then (
		Some (Var v)
	      )
	      else
		acc
		  
	  )
	| _ -> acc
	    
	    
  ) None ctxt
;;
    


let rec get_instance ty d def =
  match d with
    | [] -> None
    | (hd1, (hd2, hd3, hd4))::tl ->

	let (largs, ccl) = decomp_foralls hd3 in
	  match unification_term ty ccl (term_var ty) def with
	    | Mgu s -> (
		let args =
		    List.fold_left (

		      fun acc hd ->

			let (hd1, hd2) = hd in
			  
			  acc @ (
			    match find_list s hd1 with
			      | None -> Avar
			      | Some t -> 
				  t
			  ) :: []


		    ) [] largs		  
		in 
		  Some (App (Cste hd1, args))
		      
	      )
	    | _ -> get_instance ty tl def


;;

let typeclass_oracle ctxt ty def =  

  (*printf "looking for: %s\n" (string_of_term ty VarMap.empty); flush stdout;*)
  (* is this a class type ?? *)
  match getsubdef "TypeClass.Definition" def with
    | None -> None
    | Some d ->
	
	let d = definition2ext ("TypeClass.Definition"::[]) d in
	let (fct, args) = decomp_app ty in
	let is_classtype =
	  List.fold_left (

	    fun acc hd -> 
	      
	      let (hd1, (hd2, hd3, hd4)) = hd in
		
	      let (fct', args') = decomp_app hd2 in
		if (term_eq fct fct' def) then 
		  true
		else
		  acc
		    
	  ) false d in
	  
	  if (not is_classtype) then
	    (* nop ... *)
	    None
	  else (
	    (* yes, so now the question is: are we looking for a well-defined instance, or just an instance defined in the context *)
	    match 
	    let fv = term_fv ty VarSet.empty in
	      if VarSet.is_empty fv then (
		
		match getsubdef "TypeClass.Instance" def with
		  | None -> None
		  | Some i ->
		      
		      let i = definition2ext ("TypeClass.Instance"::[]) i in
			get_instance ty i def

	      ) else (

		(* instance in context *)
		get_in_ctxt (rev ctxt) ty def
		  
			      
	      )
	    with
	      | None -> (*printf "looking for: %s\n" (string_of_term ty VarMap.empty); flush stdout;*) None
	      | Some a -> Some a
	  )
	    
			      
;;
