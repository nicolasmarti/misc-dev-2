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

open Listext;;
open Varset;;
open Def;;
open Term;;
open Unification;;
open Rewrite;;
open String;;
open Printf;;
open Printer;;
open Freshness;;
open Definition;;

(* Automatic generation of induction principles *)

(* generation of induction type *)

let rec ind_princ_cons_ind_hyp lqv ind_name consnum varnum pred ind_args ind_type_hyp def =
  match lqv with
    | [] -> []
    | (hd1, hd2) :: tl ->
        let tl' = (ind_princ_cons_ind_hyp tl ind_name consnum (varnum + 1) pred ind_args ind_type_hyp def) in
        let (fct, args) = (decomp_app hd2) in
        let pred_args = (
          match (unification_listterm (list_name2list_var (list_proj1 (ind_args @ ind_type_hyp))) args VarSet.empty def) with
            | Mgu s -> 
                (*print_context (readable_context_fp (comp_subs s) state.def); printf "\n\n";*)
                apply_subs_listterm (list_name2list_var (list_proj1 (ind_type_hyp))) (comp_subs s) VarSet.empty
            | _ -> 
                (list_name2list_var (list_proj1 (ind_type_hyp)))          
        ) in
          if (fct = Var ind_name) then
            (
              (concat "" ("Pred" :: "indind" :: (string_of_int consnum) :: (string_of_int varnum) :: [])),
              app_nf (App (Var pred, pred_args @ (Var hd1)::[]))
            ) :: tl' 
          else 
            tl';;



let rec ind_princ_cons lcons ind_args pred cons_num ind_name ind_type_hyp ind_def def =
  match lcons with
    | [] -> []
    | hd :: tl ->
        let tl' = (ind_princ_cons tl ind_args pred (cons_num + 1) ind_name ind_type_hyp ind_def def) in
        let (hd_hyp, hd_concl) = (decomp_foralls hd) in
        let (hd_concl_fct, hd_concl_args) = (decomp_app hd_concl) in
        let pred_args = (
          match (unification_listterm (list_name2list_var (list_proj1 (ind_args @ ind_type_hyp))) hd_concl_args VarSet.empty def) with
            | Mgu s -> 
                (*print_context (readable_context_fp (comp_subs s) state.def); printf "\n\n";*)
                apply_subs_listterm (list_name2list_var (list_proj1 (ind_type_hyp))) (comp_subs s) VarSet.empty
            | _ -> 
                (list_name2list_var (list_proj1 (ind_type_hyp)))
        ) in
        let ind_hyp = (ind_princ_cons_ind_hyp hd_hyp ind_name cons_num 0 pred ind_args ind_type_hyp def) in

          ( concat "" (pred :: "ind" :: (string_of_int cons_num) :: []),
            (largs_foralls
               (app_nf ( App
                           (
                             App (Var pred, pred_args),
                             (App (Cons (cons_num,(Var ind_name)), (list_name2list_var (list_proj1 (ind_args @ hd_hyp))))) :: []                  
                           )
               )
               )
                   
               (hd_hyp @ ind_hyp)
            )
          ) :: tl';;

let ind_princ_type ind_name ind_args ind_type ind_cons def =
  let v = fresh_name_list_name (term_var (Ind (ind_name, ind_args, ind_type, ind_cons))) "x" in 
  let pred = fresh_name_list_name (v ++ (term_var (Ind (ind_name, ind_args, ind_type, ind_cons)))) "Pred" in 
  let (ind_type_hyp, ind_type_concl) = (decomp_foralls ind_type) in
  let ind_princ_hyp = (ind_princ_cons ind_cons ind_args pred 0 ind_name ind_type_hyp (Var ind_name) def) in
    (largs_foralls
       
       (app_nf (App (Var pred, (list_name2list_var (list_proj1 ind_type_hyp) @ (Var v)::[]))))
       
       (ind_args @ 
           (pred, largs_foralls (Forall (v, App (Var ind_name, list_name2list_var (list_proj1 (ind_args @ ind_type_hyp))), Type)) ind_type_hyp) :: 
           ind_princ_hyp @ 
           ind_type_hyp @ 
           (v, app_nf (App (Var ind_name, list_name2list_var (list_proj1 (ind_args @ ind_type_hyp))))) :: 
           []
       )
    );;

(* generation of induction principle *)

let rec ind_princ_dest_rec_hyp lqv ind_name ind_type_hyp ind_args def =
  match lqv with
    | [] -> []
    | (hd1, hd2) :: tl ->
        let tl' = (ind_princ_dest_rec_hyp tl ind_name ind_type_hyp ind_args def) in
        let (fct, args) = (decomp_app hd2) in
        let pred_args = (
          match (unification_listterm (list_name2list_var (list_proj1 (ind_args @ ind_type_hyp))) args VarSet.empty def) with
            | Mgu s -> 
                apply_subs_listterm (list_name2list_var (list_proj1 (ind_type_hyp))) (comp_subs s) VarSet.empty
            | _ -> 
                (list_name2list_var (list_proj1 (ind_type_hyp)))
        ) in
          if (fct = Var ind_name) then
            (app_nf
                (App
                    (Var (concat "" (ind_name :: "induc" :: [])),
                    pred_args @ (Var hd1)::[])
                ) :: tl' 
            )
          else 
            tl';;


let rec ind_princ_dest lcons ind_args ind_name cons_num pred ind_type_hyp def =
  match lcons with
    | [] -> []
    | hd :: tl ->
        let tl' = (ind_princ_dest tl ind_args ind_name (cons_num + 1) pred ind_type_hyp def) in
        let (cons_hyp, cons_concl) = (decomp_foralls hd) in
          (largs_lambdas
             (app_nf
                 (App
                     (Var (concat "" (pred :: "ind"  :: (string_of_int cons_num) :: [])),                 
                     (list_name2list_var (list_proj1 cons_hyp)) @
                       (ind_princ_dest_rec_hyp cons_hyp ind_name ind_type_hyp ind_args def)
                     )
                 )
             )
             (ind_args @ cons_hyp)
          ) :: tl';;

let ind_princ_pf ind_name ind_args ind_type ind_cons def =
  let v = fresh_name_list_name (term_var (Ind (ind_name, ind_args, ind_type, ind_cons))) "x" in 
  let pred = fresh_name_list_name (v ++ (term_var (Ind (ind_name, ind_args, ind_type, ind_cons)))) "Pred" in 
  let (ind_type_hyp, ind_type_concl) = (decomp_foralls ind_type) in
  let ind = (Ind(ind_name, ind_args, ind_type, ind_cons)) in
  let ind_princ_hyp = (ind_princ_cons ind_cons ind_args pred 0 ind_name ind_type_hyp ind def) in
  let dest = (ind_princ_dest ind_cons ind_args ind_name 0 pred ind_type_hyp def) in
  let cur_ind_type = App (Var ind_name, list_name2list_var (list_proj1 (ind_args @ ind_type_hyp))) in
    (largs_lambdas
       ( Phi 
           (
             (concat "" (ind_name :: "induc" :: [])) , 
             ind_type_hyp @ (v, cur_ind_type) ::[],
             (
               (App (Var pred, (list_name2list_var (list_proj1 ind_type_hyp) @ (Var v)::[])))
                 
             ),
             Some ((List.length ind_type_hyp) :: []),
             (
               ( Match 
                   (
                     (Var v),                        
                     (dest),
                     Some (app_nf (App (Var pred,(list_name2list_var (list_proj1 ind_type_hyp) @ (Var v)::[])))),
		     None
                   )
               )                
             )
           )
       )
       
       (
         ind_args @  
           (pred, largs_foralls (Forall (v, cur_ind_type, Type)) ind_type_hyp) :: ind_princ_hyp
       )
    );;
