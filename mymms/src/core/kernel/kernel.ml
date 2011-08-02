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

(*
  
  Here we should have a function that:
  1) verifies that a term finishes
  2) that the inductive typess are wf
  3) that the types is well checked
  -> what to do if there are some free variables ?? --> add some implicite arguments ?

*)

open Listext;;
open Termchecker;;
open Indwf;;
open Arith;;
open Term;;
open Alpha;;
open Varset;;
open Varmap;;
open Simpl;;
open List;;
open Rewrite;;
open Printf;;
open Printer;;
open Fold;;
open Termeq;;
open Definition;;
open Def;;
open Output;;
open Freshness;;
open Random;;

let rec check_term_wctxt domain ctxt te ty def coercion oracles overload implicite =
  self_init ();
  Freshness.gfv := VarSet.empty;
  let bv = (listvarterm2varset ctxt) in
  let te = var2cste_implicite te def overload implicite in
  let te = alpha_term_vars te (bv +++ ((definition2nameset def) +++ (vmdomain overload))) in
  let te = app_nf (term_diff te bv VarSet.empty) in
    tcgfv.gfv <- (term_fv te bv);
    tcgfv.domain <- domain;
    let ty = (
      match ty with
        | None -> None
        | Some ty ->
            let ty = var2cste_implicite ty def overload implicite in
            let ty = alpha_term_vars ty (bv +++ ((definition2nameset def) +++ (vmdomain overload))) in
            let ty = app_nf (term_diff ty bv tcgfv.gfv) in
              tcgfv.gfv <- tcgfv.gfv +++ (term_fv ty bv); Some (ty)
    ) in
      (*printf "well-formed\n\n"; flush stdout;*)
    let l = termcheck ctxt te ty bv def coercion oracles overload implicite (BTrue, []) in
    let (result, _, errs) =
      List.fold_left (
        fun tl' hd ->
          let (ctxt2, te, ty2, s) = hd in
	    if (not (indwf te && indwf ty2)) then tl' else
	      let size = term_size_int te in
              let ctxt2 = subs_filter2 ctxt2 ((term_fv te bv) +++ (term_fv ty2 bv)) in
		(*
		printf "set of free var:%s\n\n" (string_of_listterm (List.map (fun x -> Var x) (VarSet.elements ((term_fv te bv) +++ (term_fv ty2 bv)))) VarMap.empty);
		printf "set of free var:%s\n\n" (string_of_listvarterm ctxt2 VarMap.empty);
		*)
		match ctxt2 with
		  | [] -> (
		      let newres = (
			match ty with
			  | None -> Some (te, fold ty2 bv def)
			  | Some ty ->
			      let ty = apply_subs_term ty s bv in
				if (term_eq ty ty2 def) then
				  Some (te, ty)
				else
				  Some (te, fold ty2 bv def)
		      ) in
			match tl' with
			  | (Some te', Some size', err') -> (
			      if (size' < size) then
				tl'
			      else
				(newres, Some size, err')
			    )
			  | (_, _, err') -> (newres, Some size, err')
		    )
		  | l -> (

		      (*
			ote should be a complete term if Some
			if None -> cannot find the terms to replace the free variable
		      *)
		      let ote = (
			(* we do a traversal of the free variables/types *)
			List.fold_left (
			  fun acc hd ->
			    match acc with
				(* if we were not able to resolve previous variable we give up*)
			      | (None, v) -> (None, v)
				  (* else we continue *)
			      | (Some (te, ty), _) -> (
				  let (x, ty') = hd in
				    (* look for a solution provided by oracles *)
				    
				  let sol =
				    (* lets check all the oracles *)
				    List.fold_left (
				      fun acc hd ->
					(* lets ask the oracles for a term *)
					match hd ctxt ty' def with
					  | None -> acc
					  | Some proof ->
					      (* and verify the answer *)
					      match check_term_wctxt domain ctxt proof (Some ty') def coercion oracles overload implicite with
						  (* not a good solution, lets try the next one  *)
						| None -> acc
						    (* seems to be a good solution, we return it *)
						| Some (te, ty) ->
						    Some te
				    ) None oracles in

				    match sol with
					(* if no solution we give up*)					  
				      | None ->
					  (*
					    printf "unresolved  (%s: %s) in  (%s: %s)\n\n" (string_of_term (Var x) VarMap.empty) (string_of_term ty' VarMap.empty) (string_of_term te VarMap.empty) (string_of_term ty VarMap.empty);
					  *)
					  (None, Some ((Var x), ty', te, ty))
					    (* else we rewrite and continue *)
				      | Some (xte) ->
					  (Some (
					    rewrite_term_var_term te x xte,
					    rewrite_term_var_term ty x xte
					  ), None)
				)
				  
			) (Some (te, ty2), None) l 
		      ) in
			match ote with
			  | (None, Some err) -> 
			      let (hd1, hd2, hd3) = tl' in
				(hd1, hd2, err :: hd3)				  
			  | (Some (ote, oty), None) -> (
			      let size = term_size_int ote in				  
				match tl' with
				  | (Some te', Some size', err') -> (
				      if (size' < size) then
					tl'
				      else
					(Some (ote, oty), Some size, err')
				    )
				  | (_, _, err') -> (Some (ote, oty), Some size, err')
			    )
			  | _ -> (* should never be here *) raise (Failure "Fatal Grave Error (kernel.ml)")
		    )
      ) (None, None, []) l              
    in
      match result with
	| Some (te, ty) -> (match termcheck ctxt ty (Some Type) bv def coercion oracles overload implicite (BTrue, []) with
			      | ([],ty, tyty, s)::tl -> Some (te, ty)
			      | _ -> print_error "type not of type Type\n\n"; None
			   )
	| None ->
	    print_error "termchecking error (incomplete inference)!\n\n";
	    List.fold_left (
	      fun acc hd ->
		let (hd1, hd2, hd3, hd4) = hd in
		  print_error (sprintf "unresolved  (%s: %s) in  (%s: %s)\n\n" (string_of_term hd1 VarMap.empty) (string_of_term hd2 VarMap.empty) (string_of_term hd3 VarMap.empty) (string_of_term hd4 VarMap.empty));
	    ) () errs;
	    None              
;;

let simpl_term_wctxt domain ctxt te ty def coercion oracles overload implicite =
  match check_term_wctxt domain ctxt te ty def coercion oracles overload implicite with
    | None -> None
    | Some (te, ty) ->
        (*Some (simpl te def, ty)*)
	Some (fold_term (simpl te def) VarSet.empty def, ty)
;;

let compute_term_wctxt domain ctxt te ty def coercion oracles overload implicite =
  match check_term_wctxt domain ctxt te ty def coercion oracles overload implicite with
    | None -> None
    | Some (te, ty) ->
        (*Some (simpl te def, ty)*)
	Some (fold_term (simpl te def) VarSet.empty def, ty)
;;

let check_term domain te ty def coercion oracles overload implicite =
  check_term_wctxt domain [] te ty def coercion oracles overload implicite 
;;

let simpl_term domain te ty def coercion oracles overload implicite =
  simpl_term_wctxt domain [] te ty def coercion oracles overload implicite
;;

let compute_term domain te ty def coercion oracles overload implicite =
  compute_term_wctxt domain [] te ty def coercion oracles overload implicite
;;

