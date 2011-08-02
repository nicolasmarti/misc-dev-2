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

open Printf;;
open List;;
open String;;
open Varset;;
open Freshness;;
open Def;;
open Term;;
open Rewrite;;
open Alpha;;
open Unfold;;
open Printer;;

(* 
   beta reduction:
  
   lazy tactic, after typechecking

   w.o. unfolding

*)

let rec beta_red t (def: definition) =
(*
  printf "beta_red: ";
  print_term t;
  printf "\n\n";
*)
  match (app_nf t) with
    | App (t1 , t2) -> (
        match t1 with
          | Lambda (x, t11, t12) -> (
              match t2 with
                | [] -> t1
                | hd :: [] ->
                    let t12' = (rewrite_term_var_term (alpha_term_vars t12 (term_fv hd VarSet.empty)) x hd) in
                      beta_red t12' def
                | hd :: tl ->
                    let t12' = (rewrite_term_var_term (alpha_term_vars t12 (term_fv hd VarSet.empty)) x hd) in
                      beta_red (App (t12', tl)) def
            )
          | Phi (x, largs, ty, ldecargs, te) -> (
              if (List.length t2 < List.length largs) then
                t
              else (
                let te' = (rewrite_term_var_term te x (Phi (x, largs, ty, ldecargs, te))) in
                let t1' = (largs_lambdas te' largs) in
                  beta_red (App (t1', t2)) def
              )
            )
          | App (t11, t12) -> (
                beta_red (app_nf t) def
            )
          | ( Cste x ) -> (
              let t1' = (unfold_term t1 def) in
                match t1' with
                  | Lambda (_,_,_) -> beta_red (App (t1', t2)) def
                  | Phi (_,_,_,_,_) -> beta_red (App (t1', t2)) def
                  | Cste c -> 
		      if (c = x) then
			(App (Cste x, t2))
		      else
			beta_red (App (t1', t2)) def
                  | Obj _ -> beta_red (App (t1', t2)) def
                  | _ -> App (t1, t2)
            )
          | Match (t11,ldes, t12, ind) ->
              let t1' = beta_red (Match (t11, ldes, t12, ind)) def in
                if (t1 = t1') then
                  (app_nf t)
                else
                  beta_red (App (t1', t2)) def           
          | Obj o -> (
              o#exec t2 def
            )
	      
	  (* in the remaining case is the AdvMAtch --> raise exception ??? *)
          | _ -> (app_nf t)

      )
    | Match (t11,ldes, t12, ind) ->
        let t11' = beta_red t11 def in
        let (t11, t12) = (decomp_app (unfold_term t11' def)) in (            
          match t11 with
            | (Cons (n, _)) ->
                beta_red (App (List.nth ldes n, t12)) def
            | _ -> (app_nf t)
        )
    | Forall (x, t11, t12) ->
        Forall (x, t11, t12)
    | Cons (n, t1) ->
        Cons (n, t1)
    | Let (x, t1, t2) ->
	let t1 = beta_red t1 def in
	  beta_red (rewrite_term_var_term (alpha_term_vars t2 (term_fv t1 VarSet.empty)) x t1) def
    | _ -> (app_nf t)
;;
