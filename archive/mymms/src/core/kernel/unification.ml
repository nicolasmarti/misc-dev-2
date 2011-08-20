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
open Varmap;;
open Freshness;;
open Def;;
open Term;;
open Rewrite;;
open Alpha;;
open Beta;;
open Printer;;
open Termeq;;
open Unfold;;
open Unfoldbetared;;
open Fold;;
open Listext;;

(* 
   unification:
   
      Mgu s <-> t1.s =_{alpha} t2.s
      DnkMgu <-> we do not know if there is a Mgu
      NoMgu <-> ~ (E s. t1.s =_{alpha} t2.s)

   Both term must be beta reduced (??? -> match ???)

   w.o. unfolding

   App normalized
   
*)

let rec unification_term t1 t2 bv def =
(*  
  printf "-------Unification--------\n";
  printf "bv:={%s }\n\n" (
    
    List.fold_left (

      fun acc hd ->
	
	concat "" (acc :: " " :: hd :: [])

    ) "" (VarSet.elements bv)
  );
  print_term t1 VarMap.empty; printf "\n";
  printf "\t\tU\n";
  print_term t2 VarMap.empty; printf "\n";
  printf "--------------------------\n\n";
  flush stdout;
*)

  match (t1, t2) with
    | (Var x1, Var x2) ->
        if (x1 = x2) then 
          Mgu [] 
        else (
          
          match (VarSet.subset (VarSet.singleton x1) bv, VarSet.subset (VarSet.singleton x2) bv) with
            | (true, true) -> NoMgu
            | (true, false) -> Mgu ((x2, t1)::[])            
            | _ -> Mgu ((x1, t2)::[])            

        )
    | (Var x1, _) ->
        if (VarSet.subset (VarSet.singleton x1) ((term_fv t2 VarSet.empty) +++ bv)) then
          DnkMgu else
          Mgu ((x1, t2)::[])
    | (_, Var x2) ->
        if (VarSet.subset (VarSet.singleton x2) ((term_fv t1 VarSet.empty) +++ bv)) then
          DnkMgu else
          Mgu ((x2, t1)::[])
    | (Cons (n0, t1), Cons (n1, t2)) ->
        if (n0 = n1) then (
          if (term_eq t1 t2 def) then
            Mgu []
          else
            DnkMgu
        ) else
          NoMgu
    | (Lambda(x1,t11,t12), Lambda(x2, t21, t22)) -> (
        match (unification_term t11 t21 bv def) with
          | NoMgu -> NoMgu
          | DnkMgu -> DnkMgu
          | Mgu u ->
              match 
                unification_term 
                  (apply_subs_term t12 (comp_subs u) bv)
                  (apply_subs_term (rewrite_term_var_term t22 x2 (Var x1)) (comp_subs u) bv)
                  (x1 ++ bv)
                  def
              with
                | NoMgu -> NoMgu
                | DnkMgu -> DnkMgu
                | Mgu u' -> Mgu (u @ u')
                    
      )
    | (Forall(x1,t11,t12), Forall(x2, t21, t22)) -> (
        match (unification_term t11 t21 bv def) with
          | NoMgu -> NoMgu
          | DnkMgu -> DnkMgu
          | Mgu u ->
              match 
                unification_term 
                  (apply_subs_term t12 (comp_subs u) bv)
                  (apply_subs_term (rewrite_term_var_term t22 x2 (Var x1)) (comp_subs u) bv)
                  (x1 ++ bv)
                  def
              with
                | NoMgu -> NoMgu
                | DnkMgu -> DnkMgu
                | Mgu u' -> Mgu (u @ u')
      )

    (* Is this correct ??? not for mutual inductive *)
    | (Ind (x1, la1, ty1, lc1), Ind (x2, la2, ty2, lc2)) -> (

	let laty1 = fold_term (unfold_term_fp (largs_foralls ty1 la1) def) bv def in
	let lalc1 = fold_listterm (unfold_listterm_fp (largs_foralls_listterm lc1 la1) def) (x1 ++ bv) def in
	let laty2 = fold_term (unfold_term_fp (rewrite_term_var_term (largs_foralls ty2 la2) x2 (Var x1)) def) bv def in
	let lalc2 = fold_listterm (unfold_listterm_fp (rewrite_listterm_var_term (largs_foralls_listterm lc2 la2) x2 (Var x1)) def) (x1 ++ bv) def in
	  
	  unification_listterm (laty1::lalc1) (laty2::lalc2) (x1 ++ bv) def
	

      )
    | (App (fct1, args1), App (fct2, args2)) -> (
	let (f1, a1) = decomp_app t1 in
	let (f2, a2) = decomp_app t2 in
	let (fct1, args1, fct2, args2) = (
	  if (List.length a1 > List.length a2) then (
	    (App (fct1, nth_head (List.length a1 - List.length a2) a1), nth_tail (List.length a1 - List.length a2) a1, fct2, a2)
	  ) else 
	    if (List.length a1 < List.length a2) then (
	      (fct1, a1, App (fct2, nth_head (List.length a2 - List.length a1) a2), nth_tail (List.length a2 - List.length a1) a2)
	    ) else (f1, a1, f2, a2)
	) in	  
        match (unification_term fct1 fct2 bv def) with
          | NoMgu -> NoMgu
          | DnkMgu -> DnkMgu
          | Mgu u ->	      
              match (unification_listterm 
                        (apply_subs_listterm args1 (comp_subs u) bv)
                        (apply_subs_listterm args2 (comp_subs u) bv)
                        bv
                        def
              ) with
                | NoMgu -> NoMgu
                | DnkMgu -> DnkMgu
                | Mgu u' ->
                    Mgu (u @ u')
      )              
    | (Type,Type) -> Mgu []

(*

  TODO for the NoMgu case

    | (Ind (x1, la1, ty1, lc1), Ind (x2, la2, ty2, lc2)) -> (
	

      )
*)    

    | (Cste v1, Cste v2) ->
        if (v1 = v2) then
          Mgu []
        else
          if (term_eq t1 t2 def) then Mgu [] else NoMgu
	    
    | (Cste c1, _) ->
        unification_term (unfold_term t1 def) t2 bv def
    | (_, Cste c2) ->
        unification_term t1 (unfold_term t2 def) bv def
    | (Avar, _) -> DnkMgu
    | (_, Avar) -> DnkMgu
    | (AdvMatch (_, _,_) , _) -> DnkMgu

    | (_, AdvMatch (_, _,_)) -> DnkMgu

    | (t1, t2) ->
        if (term_eq t1 t2 def) then
          Mgu []
        else (
          (* bonjour rustine !!! *)
          let (t1', _) = decomp_app (beta_red t1 def) in
          let (t2', _) = decomp_app (beta_red t2 def) in (
	      (*printf "last case (%s Vs %s)\n\n" (string_of_term t1' VarMap.empty) (string_of_term t2' VarMap.empty); flush stdout;*)
            match (t1',t2') with
              | (Cons (n1, t1), Cons (n2, t2)) ->
                  if (not (n1 = n2)) then NoMgu else DnkMgu                    
              | (Cste c1, _) ->
                  unification_term (unfold_term (beta_red t1 def) def) t2 bv def
              | (_, Cste c2) ->
                  unification_term t1 (unfold_term (beta_red t2 def) def) bv def
              | _ -> (
		  (*
                  printf "No unification between: %s Vs %s\n" 
		    (string_of_term t1 VarMap.empty) 
		    (string_of_term t2 VarMap.empty);
		  *)
                  DnkMgu
		)
          )       
        )
and unification_listterm l1 l2 bv def =
  match (l1, l2) with
    | ([],[]) -> Mgu []
    | (hd1::tl1, hd2::tl2) ->(
        match (unification_term hd1 hd2 bv def) with
          | NoMgu -> NoMgu
          | DnkMgu -> DnkMgu
          | Mgu u ->
              match (unification_listterm (apply_subs_listterm tl1 (comp_subs u) bv) (apply_subs_listterm tl2 (comp_subs u) bv) bv def) with
                | NoMgu -> NoMgu
                | DnkMgu -> DnkMgu
                | Mgu u' -> Mgu (u @ u')
      )
    | _ -> NoMgu
;;
