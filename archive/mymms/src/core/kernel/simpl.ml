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
open Term;;
open Varset;;
open Varmap;;
open Rewrite;;
open Alpha;;
open Unfold;;
open Printf;;
open Printer;;

(*************************)

let rec nomatch t bv =
  match t with
    | Obj o -> true
    | Cste x -> true
    | Var x -> true
    | Type -> true
    | Let (x, t1,t2) -> (nomatch  t1 bv) && (nomatch  t2 (x ++ bv))
    | Lambda (x, t1,t2) -> (nomatch  t1 bv) && (nomatch  t2 bv)
    | Forall (x, t1,t2) -> (nomatch  t1 (x ++ bv)) && (nomatch  t2 (x ++ bv))
    | Ind (x, t1,t2, t3) -> true
    | Phi (x, t1,t2,n, t3) -> (nomatch  t2 (x ++ bv)) && 
          (nomatch  t3 (x ++ (bv +++ (listvarterm2varset t1))))
    | Cons (n, t1) -> (nomatch  t1 bv)
    | App (t1,t2) -> (nomatch t1 bv) && (nomatch_list t2 bv)
    | Match (t1, t2, t3, ind) -> (
        match t1 with
          | Var x -> if (VarSet.subset (VarSet.singleton x) bv) then (nomatch_list t2 bv) else false
          | _ -> false
      )
    | AdvMatch (t1, t2, t3) -> (
        match t1 with
          | Var x -> if (VarSet.subset (VarSet.singleton x) bv) then (nomatch_listtermterm t2 bv) else false
          | _ -> false
      )
    | Avar -> true

and nomatch_list l bv =
  match l with
    | [] -> true
    | hd::tl -> (nomatch hd bv) && (nomatch_list tl bv)
and nomatch_listtermterm l bv =
  match l with
    | [] -> true
    | (hd1, hd2) :: tl ->
	(nomatch hd2 (bv +++ (term_var hd1))) && (nomatch_listtermterm tl bv);;

let rec simpl t def =

(*
    printf "simpl_term: ";
    print_term t VarMap.empty;
    printf "\n\n";
*)

  let t = (app_nf t) in

  let nt = (
    match t with
      | App (t1 , t2) -> (
          match t1 with
            | Lambda (x, t11, t12) -> (
		match t2 with
                  | [] -> simpl t1 def
                  | hd :: [] ->
                      let t12' = (rewrite_term_var_term (alpha_term_vars t12 (term_fv hd VarSet.empty)) x hd) in
			simpl t12' def
                  | hd :: tl ->
                      let t12' = (rewrite_term_var_term (alpha_term_vars t12 (term_fv hd VarSet.empty)) x hd) in
			simpl (App (t12', tl)) def
              )
            | Phi (x, largs, ty, ldecargs, te) -> (
		if (List.length t2 < List.length largs 
		    (*|| not (VarSet.is_empty (List.fold_left (fun acc hd -> let a = List.nth t2 hd in acc +++ (term_fv a VarSet.empty)) VarSet.empty ldecargs))*)) then
                  App(t1, simpl_listterm t2 def)
		else (
                  let te' = (rewrite_term_var_term te x (Phi (x, largs, ty, ldecargs, te))) in
                  let t1' = (largs_lambdas te' largs) in
                  let t' = simpl (App (t1', t2)) def in
                    if (nomatch t' VarSet.empty) then
                      t' 
                    else
                      App(t1, simpl_listterm t2 def)
		)
              )
            | App (t11, t12) -> (
		simpl (app_nf t) def
              )
            | ( Cste x ) -> (
		let t1' = (app_nf (unfold_term t1 def)) in
                  match t1' with
                    | Lambda (_,_,_) -> 
			if (List.length t2 >= 1) then (
                          let t' = simpl (App (t1', t2)) def in
			    if (nomatch t' VarSet.empty) then
			      t' 
			    else
			      App (Cste x, simpl_listterm t2 def)
			)
			else
                          App (Cste x, simpl_listterm t2 def)
                    | Phi (v, largs, ty, ldecargs, te) -> (
			if (List.length t2 < List.length largs 
			    (*|| not (VarSet.is_empty (List.fold_left (fun acc hd -> let a = List.nth t2 hd in acc +++ (term_fv a VarSet.empty)) VarSet.empty ldecargs))*)
			      ) then
                          App (Cste x, simpl_listterm t2 def)
			else (
                          let te' = (rewrite_term_var_term te v (Cste x)) in
                          let t1' = (largs_lambdas te' largs) in
                          let t' = simpl (App (t1', t2)) def in
                            if (nomatch t' VarSet.empty) then
                              t' 
                            else (
                              App (Cste x, simpl_listterm t2 def)
                            )
			)
                      )
                    | Cste c -> 
			if (c = x) then
			  (App (Cste c, simpl_listterm t2 def))
			else simpl (App (t1', t2)) def
                    | Obj o -> simpl (App (t1', t2)) def
                    | App (t11, t12) -> (                      
                      match t11 with 
                        | Cste c -> simpl (App (Cste c, t12 @ t2)) def
                        | _ -> App (t1, simpl_listterm t2 def)
                    )
                  | _ -> App (t1, simpl_listterm t2 def)
            )
          | Match (t11,ldes, t12, ind) ->
              let t1' = simpl (Match (t11, ldes, t12, ind)) def in
                if (t1 = t1') then
                  (app_nf (App(t1, simpl_listterm t2 def)))
                else
                  simpl (App (t1', t2)) def                
          | Obj o -> (
	      let t2 = simpl_listterm t2 def in
	      let t2 = List.map (fun hd -> unfold_object hd hd def) t2 in
	      let res = o#exec t2 def in
              let (t1, t2) = (decomp_app res) in 
		match t1 with
		  | Obj o2 ->
		      if (o#equal o2) then
			res 
		      else
			simpl res def
		  | _ -> simpl res def
	      
            )
          | _ -> App (t1, simpl_listterm t2 def)
      )
    | Match (t11,ldes, t12, ind) ->
        let t11' = simpl t11 def in
        let (t11, t12') = (decomp_app t11') in (            
          match t11 with
            | (Cons (n, _)) ->
                simpl (App (List.nth ldes n, t12')) def
            | Cste c -> (
		let t' = unfold_term (Cste c) def in
		  match t' with
		    | Cste x ->
			if x = c then			  
			  (Match (App (t', t12'), ldes, t12, ind))
			else
			  simpl (Match (App (t', t12'), ldes, t12, ind)) def
		    | _ -> simpl (Match (App (t', t12'), ldes, t12, ind)) def
	      )
            | _ -> Match (t11', ldes, t12, ind)
        )
    | Forall (x, t11, t12) ->
        Forall (x, simpl t11 def, simpl t12 def)
    | Lambda (x, t11, t12) ->
        Lambda (x, simpl t11 def, simpl t12 def)
    | Cons (n, t1) ->
        Cons (n, t1)
    | Let (x, t1, t2) ->
	let t1 = simpl t1 def in
	  simpl (rewrite_term_var_term (alpha_term_vars t2 (term_fv t1 VarSet.empty)) x t1) def
    | Obj o -> o#exec [] def
    | _ -> (app_nf t)
  ) in
    if (nomatch nt VarSet.empty) then
      nt
    else (
      t
    )    
and simpl_listterm l def =
  match l with 
    | [] -> []
    | hd :: tl ->
        (simpl hd def) :: (simpl_listterm tl def)

and unfold_simpl te def =
  (*printf "unfold_simpl: "; print_term te VarMap.empty; printf "\n"; flush stdout;*)
  let te' = (unfold_term te def) in
    (*printf "prout\n%s\n" (string_of_term te' VarMap.empty); flush stdout;*)
    if (te = te') then
      te else      
	match te' with
	  | Ind _ -> te'
	  | App (_, _) ->
	      let te'' = (simpl te' def) in
		(*printf "prout2\n\n"; flush stdout;*)
		if (te'' = te') then
		  te'
		else
		  unfold_simpl te'' def
	  | _ -> te'

and unfold_object te orig def =
  let te' = (unfold_term te def) in
    (*printf "prout\n%s\n" (string_of_term te' VarMap.empty); flush stdout;*)
    if (te = te') then
      orig else      
	match simpl te' def with
	  | Obj o -> Obj o
	  | Cste _ -> unfold_object te' orig def
	  | _ -> orig
    

;;
