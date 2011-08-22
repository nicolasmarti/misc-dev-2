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
open Printer;;
open List;;
open String;;
open Varset;;
open Freshness;;
open Def;;
open Term;;
open Rewrite;;
open Alpha;;
open Beta;;
open Unfold;;
open Unfoldbetared;;
open Varmap;;
open Output;;

(*
  term equivalence:

  after beta reduction (implying App normalized)

  use: only on types
  
*)

let rec term_eq t1 t2 def =
  
  (*
    printf "\n(";
    print_term t1 VarMap.empty;
    printf "\n,\n";
    print_term t2 VarMap.empty;
    printf ")\n";
  *)

  (* REDO *)

  (*  match (beta_red (unfold_term t1 def) def, beta_red (unfold_term t2 def) def) with*)
  match (
    match (t1, t2) with

      (* Is this the good way to do *)
      | (Obj o1, Obj o2) -> 
	  (o1#equal o2)
        
      | (Var v1, Var v2) -> v1 = v2
      
      | (Lambda (x1, t11, t12), Lambda (x2, t21, t22)) ->
          let bv' = (x1 ++ (x2 ++ ((term_var t12) +++ (term_var t22)))) in
          let x = (fresh_name_list_name bv' x1) in
          let t12' = (rewrite_term_var_term t12 x1 (Var x)) in
          let t22' = (rewrite_term_var_term t22 x2 (Var x)) in
            (term_eq t11 t21 def && term_eq t12' t22' def)
              
      | (Forall (x1, t11, t12), Forall (x2, t21, t22)) ->
          let bv' = (x1 ++ (x2 ++ ((term_var t12) +++ (term_var t22)))) in
          let x = (fresh_name_list_name bv' x1) in
          let t12' = (rewrite_term_var_term t12 x1 (Var x)) in
          let t22' = (rewrite_term_var_term t22 x2 (Var x)) in
            (term_eq t11 t21 def && term_eq t12' t22' def)
              
      | (Phi (x1, largs1, ty1, ldec1, te1), Phi (x2, largs2, ty2, ldec2, te2)) ->
          let bv' = (x1 ++ (x2 ++ ((listvarterm2varset largs1) +++ (listvarterm2varset largs2) +++ (term_var te1) +++ (term_var te2)))) in
          let x = (fresh_name_list_name bv' x1) in
          let te1' = (rewrite_term_var_term te1 x1 (Var x)) in
          let te2' = (rewrite_term_var_term te2 x2 (Var x)) in          
          let t1' = (largs_lambdas te1' largs1) in
          let t2' = (largs_lambdas te2' largs2) in
          let ty1' = (largs_lambdas ty1 largs1) in
          let ty2' = (largs_lambdas ty2 largs2) in
            (ldec1 = ldec2 && (* pas sur d'avoir a verifier ca (assume typechecked) *)
                term_eq ty1' ty2' def &&
                term_eq t1' t2' def
            )

      | (Ind (x1, largs1, ty1, lcons1), Ind (x2, largs2, ty2, lcons2)) ->
          let bv' = (x1 ++ (x2 ++ ((listvarterm2varset largs1) +++ (listvarterm2varset largs2) +++ (listterm_var lcons1) +++ (listterm_var lcons2)))) in
          let x = (fresh_name_list_name bv' x1) in
          let lcons1' = (rewrite_listterm_var_term lcons1 x1 (Var x)) in
          let lcons2' = (rewrite_listterm_var_term lcons2 x2 (Var x)) in
          let lcons1'' = (largs_lambdas_listterm lcons1' largs1) in
          let lcons2'' = (largs_lambdas_listterm lcons2' largs2) in
          let ty1' = (largs_lambdas ty1 largs1) in
          let ty2' = (largs_lambdas ty2 largs2) in
            (term_eq ty1' ty2' def && listterm_eq lcons1'' lcons2'' def)        

      | (Match (t11, t12, t13, ind1), Match (t21, t22, t23, ind2)) ->
          (* pas sur d'avoir a verifier l'egalite sur l'indication de type *)
          (term_eq t11 t21 def && listterm_eq t12 t22 def)

      | (Cons (n1, t11), Cons (n2, t21)) ->
          n1 = n2 &&
              term_eq t11 t21 def

      | (Type, Type) -> true

      | (Cste v1, Cste v2) ->
          if (v1 = v2) then
            true
          else
            let t1' = (unfold_term t1 def) in
            let t2' = (unfold_term t2 def) in
              if ((t1 <> t1') || (t2 <> t2')) then
                term_eq t1' t2' def
              else
                false

      | (Cste v, _) ->
          if (unfold_term t1 def = Cste v) then
            (false)
          else
            term_eq (unfold_term t1 def) t2 def
      | (_, Cste v) ->
          if (unfold_term t2 def = Cste v) then
            (false)
          else
            term_eq t1 (unfold_term t2 def) def

      | (App (Cste v, _), _) ->
          if (unfold_term t1 def = t1) then
            (false)
          else
            term_eq (beta_red (unfold_term t1 def) def) t2 def

      | (_, App (Cste v, _)) ->
          if (unfold_term t2 def = t2) then
            (false)
          else
            term_eq t1 (beta_red (unfold_term t2 def) def) def
              
      | (App (Lambda (_, _, _), _), _) ->
          let t1' = (beta_red t1 def) in
            if (t1 = t1') then
              false
            else
              term_eq t1' t2 def
      | (_, App (Lambda (_, _, _), _)) ->
          let t2' = (beta_red t2 def) in
            if (t2 = t2') then
              false
            else
              term_eq t1 t2' def

      | (App (Phi (x1, t11, t12, t13, t14), t15), App(Phi (x2, t21, t22, t23, t24), t25)) ->
          (term_eq (Phi (x1, t11, t12, t13, t14)) (Phi (x2, t21, t22, t23, t24)) def && listterm_eq t15 t25 def)

      | (App (Phi (_, _, _, _,_), _), _) ->
          let t1' = (beta_red t1 def) in
            if (t1 = t1') then
              false
            else
              term_eq t1' t2 def
      | (_, App (Phi (_, _, _, _, _), _)) ->
          let t2' = (beta_red t2 def) in
            if (t2 = t2') then
              false
            else
              term_eq t1 t2' def

      | (App (t11, t12), App (t21, t22)) ->
          
          (term_eq t11 t21 def && listterm_eq t12 t22 def)


      | (Let (x, t11, t12), _) ->
	  let t1 = beta_red t1 def in
	    term_eq t1 t2 def

      | (_, Let (x, t21, t22)) ->
	  let t2 = beta_red t2 def in
	    term_eq t1 t2 def

      | (Avar, _) -> false

      | (_, Avar) -> false

      | (AdvMatch (_, _,_) , _) -> false

      | (_, AdvMatch (_, _,_)) -> false

      | _ -> 
          (
            let t1' = (beta_red (unfold_term t1 def) def) in
            let t2' = (beta_red (unfold_term t2 def) def) in
            if ((t1 <> t1') || (t2 <> t2')) then
              term_eq t1' t2' def
            else
              false
          )
  ) with
    | true -> true
    | false -> (
        false
      )
and listterm_eq l1 l2 def =
  match (l1, l2) with
    | ([], []) -> true
    | (hd1::tl1, hd2::tl2) ->
        (term_eq hd1 hd2 def && listterm_eq tl1 tl2 def)
    | _ -> false
;;


let rec rewrite_term_term_term t x y bv def =
  if (not (VarSet.equal (VarSet.empty) (VarSet.inter bv ((term_fv x VarSet.empty) +++ (term_fv y VarSet.empty))))) then
    t 
  else
    if (term_eq t x def) then y else
    (
      match t with
        | Lambda (x1, t11, t12) ->
            Lambda (x1, rewrite_term_term_term t11 x y bv def, rewrite_term_term_term t12 x y (x1 ++ bv) def)
        | Forall (x1, t11, t12) ->
            Forall (x1, rewrite_term_term_term t11 x y bv def, rewrite_term_term_term t12 x y (x1 ++ bv) def)
        | App (t11, t12) ->
            App (rewrite_term_term_term t11 x y bv def, rewrite_listterm_term_term t12 x y bv def)
        | Match (t11, t12, t13, ind) ->
            Match (rewrite_term_term_term t11 x y bv def, rewrite_listterm_term_term t12 x y bv def, 
                   (match t13 with
                      | None -> None 
                      | Some t13 -> Some (rewrite_term_term_term t13 x y bv def)
		   ),
                   (match ind with
                      | None -> None 
                      | Some ind -> Some (rewrite_term_term_term ind x y bv def)
		   )
            )
        | AdvMatch (t11, t12, t13) ->
            AdvMatch (rewrite_term_term_term t11 x y bv def, rewrite_listtermterm_term_term t12 x y bv def, 
                  match t13 with
                    | None -> None 
                    | Some t13 -> Some (rewrite_term_term_term t13 x y bv def)
            )
        | Cons (n1, t11) ->
            Cons (n1, rewrite_term_term_term t11 x y bv def)
        | Phi (x1, largs1, ty1, ldec1, te1) ->
            let (largs1', bv') = rewrite_listargs_term_term largs1 x y bv def in
            let ty1' = rewrite_term_term_term ty1 x y bv' def in
            let te1' = rewrite_term_term_term te1 x y (x1 ++ bv') def in
              Phi (x1, largs1', ty1', ldec1, te1')
        | Ind (x1, largs1, ty1, lcons1) ->
            let (largs1', bv') = rewrite_listargs_term_term largs1 x y bv def in
            let ty1' = rewrite_term_term_term ty1 x y bv' def in
            let lcons1' = rewrite_listterm_term_term lcons1 x y (x1 ++ bv') def in
              Ind (x1, largs1', ty1', lcons1')
        | _ -> t
    )
and rewrite_listterm_term_term lt x y bv def =
  match lt with
    | [] -> []
    | hd :: tl ->
        (rewrite_term_term_term hd x y bv def) :: (rewrite_listterm_term_term tl x y bv def)
and rewrite_listargs_term_term la x y bv def =
  match la with
    | [] -> ([], bv)
    | (hd1, hd2) :: tl ->
        let (tl', bv') = rewrite_listargs_term_term tl x y (hd1 ++ bv) def in
        let hd2' = rewrite_term_term_term hd2 x y bv def in
          ((hd1, hd2') :: tl', (hd1 ++ bv'))
and rewrite_listtermterm_term_term lt x y bv def =
  match lt with
    | [] -> []
    | (hd1, hd2) :: tl ->
	let hd1 = rewrite_term_term_term hd1 x y bv def in
	let hd2 = rewrite_term_term_term hd2 x y (bv +++ term_var hd1) def in
	let tl = rewrite_listtermterm_term_term tl x y bv def in
	  (hd1, hd2)::tl

;;

let rec rewrite_context_term_term c x y bv (def: definition) =
  match c with
    | [] -> []
    | (hd1, hd2) :: tl ->
        (hd1, rewrite_term_term_term hd2 x y bv def) :: (rewrite_context_term_term tl x y bv def);;
