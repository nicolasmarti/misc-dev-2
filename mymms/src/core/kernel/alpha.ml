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
open Freshness;;
open Def;;
open Term;;
open Rewrite;;

(* 
   return a term equivalent to t (through alpha reduction), without quantified variable inside bv .

   w.o. unfolding

*)

let rec alpha_term_vars t bv =
  match t with
    | Avar -> Avar
    | Obj o -> Obj o
    | Cste n -> Cste n
    | Var x -> Var x
    | Let (x, t1, t2) ->
        if (VarSet.subset (VarSet.singleton x) bv) then (
          let nv = (fresh_name_list_name (bv +++ term_var t) x) in
            Let (nv, alpha_term_vars t1 (nv ++ bv), alpha_term_vars (rewrite_term_var_term t2 x (Var nv)) (nv ++ bv))
        ) else (
            Let (x, alpha_term_vars t1 (x ++ bv), alpha_term_vars t2 (x ++ bv))
        )          
    | Lambda (x, t1, t2) ->
        if (VarSet.subset (VarSet.singleton x) bv) then (
          let nv = (fresh_name_list_name (bv +++ term_var t) x) in
            Lambda (nv, alpha_term_vars t1 (nv ++ bv), alpha_term_vars (rewrite_term_var_term t2 x (Var nv)) (nv ++ bv))
        ) else (
            Lambda (x, alpha_term_vars t1 (x ++ bv), alpha_term_vars t2 (x ++ bv))
        )          
    | Forall (x, t1, t2) ->
        if (VarSet.subset (VarSet.singleton x) bv) then (
          let nv = (fresh_name_list_name (bv +++ term_var t) x) in
            Forall (nv, alpha_term_vars t1 bv, alpha_term_vars (rewrite_term_var_term t2 x (Var nv)) (nv ++ bv))
        ) else (
            Forall (x, alpha_term_vars t1 bv, alpha_term_vars t2 (x ++ bv))
        )
    | Phi (x, t1, t2, t3, t4) ->
        if (VarSet.subset (VarSet.singleton x) bv) then (
          let nv = (fresh_name_list_name (bv +++ term_var t) x) in
          let (t1', s, bv') = (alpha_listvarterm_vars t1 bv) in
          let t2' = (rewrite_term_list_var_term t2 s) in
          let t4' = (alpha_term_vars (rewrite_term_list_var_term (rewrite_term_var_term t4 x (Var nv)) s) (nv ++ bv')) in
            Phi (nv, t1', t2', t3, t4')
        ) else (
          let (t1', s, bv') = (alpha_listvarterm_vars t1 bv) in
          let t2' = (rewrite_term_list_var_term t2 s) in
          let t4' = (alpha_term_vars (rewrite_term_list_var_term t4 s) (x ++ (bv'))) in
            Phi (x, t1', t2', t3, t4')
        )
    | Ind (x, t1, t2, t3) ->
        if (VarSet.subset (VarSet.singleton x) bv) then (
          let (t1', s, bv') = (alpha_listvarterm_vars t1 (x ++ bv)) in
          let nv = (fresh_name_list_name (bv' +++ term_var t) x) in
          let t2' = (rewrite_term_list_var_term t2 s) in
          let t3' = (alpha_listterm_vars (rewrite_list_term_list_var_term (rewrite_listterm_var_term t3 x (Var nv)) s)  (nv ++ (bv' +++ (term_var t2')))) in
            Ind (nv, t1', t2', t3')
        ) else (
          let (t1', s, bv') = (alpha_listvarterm_vars t1 bv) in
          let t2' = (rewrite_term_list_var_term t2 s) in
          let t3' = (alpha_listterm_vars (rewrite_list_term_list_var_term t3 s) (x ++ (bv' +++ (term_var t2')))) in
            Ind (x, t1', t2', t3')
        )
    | App (t1, t2) ->
        let t1' = (alpha_term_vars t1 bv) in
        let t2' = (alpha_listterm_vars t2 bv) in
          App (t1', t2')
    | Match (t1, l1, t2, ind) ->
        let t1' = (alpha_term_vars t1 bv) in
        let l1' = (alpha_listterm_vars l1 bv) in
          Match (t1', l1', t2, ind)        
    | Cons (n, l1) ->
        let l1' = (alpha_term_vars l1 bv) in
          Cons (n, l1')
    | Type -> Type
    | AdvMatch (t, ldes, ty) ->
	let t = alpha_term_vars t bv in
	let ldes = alpha_listtermterm_vars ldes bv in
	let ty = 
	  match ty with
	    | None -> None
	    | Some ty -> Some (alpha_term_vars ty bv)
	in
	  AdvMatch (t, ldes, ty)
and alpha_listterm_vars l bv =
  match l with
    | [] -> []
    | hd :: tl ->
        (alpha_term_vars hd bv) :: (alpha_listterm_vars tl bv)
and alpha_listvarterm_vars l bv =
  match l with
    | [] -> ([], [], bv)
    | (hd1, hd2) :: tl ->
        if (VarSet.subset (VarSet.singleton hd1) bv) then (
          let nv = (fresh_name_list_name bv hd1) in
          let (tl',s, bv') = (
            alpha_listvarterm_vars (rewrite_listvarterm_var_term tl hd1 (Var nv)) (nv ++ bv)
          ) in 
            ((nv,hd2) :: tl',s @ ((hd1,(Var nv))::[]), (nv ++ bv'))
        ) else (
          let (tl',s, bv') = (
            alpha_listvarterm_vars tl (hd1 ++ bv)
          ) in 
            ((hd1,hd2) :: tl',s, (hd1 ++ bv'))
        )
and alpha_listtermterm_vars l bv =
  match l with
    | [] -> []
    | (hd1, hd2) :: tl ->
	let tl = alpha_listtermterm_vars tl bv in
	let vcom = VarSet.inter (term_var hd1) bv in
	let lfv = fresh_names ((term_var hd1) +++ bv +++ (term_var hd2)) (VarSet.cardinal vcom) in
	let s = List.combine (VarSet.elements vcom) (List.map (fun x -> Var x) lfv) in
	let hd1 = apply_subs_term hd1 s VarSet.empty in
	let hd2 = alpha_term_vars hd2 ((term_var hd1) +++ bv +++ (list2varset lfv)) in
	let hd2 = apply_subs_term hd2 s VarSet.empty in
	  (hd1, hd2) :: tl
;;


let term_cf t =
  alpha_term_vars t (term_fv t VarSet.empty)  
;;
