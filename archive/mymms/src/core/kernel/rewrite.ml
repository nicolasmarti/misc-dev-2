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
open Varmap;;
open Def;;
open Term;;
open Listext;;
open Definition;;

(* rewriting of a variable x by a variable y in the term t *)
let rec rewrite_term_var_var t x y =
  match t with
    | Avar -> Avar
    | Obj o -> Obj o
    | Cste n -> Cste n
    | Var v -> 
        if (v = x) then (Var y) else (Var v)
    | Let (s, t1, t2) ->
        let nn = (
          if (s = x) then y else s
        ) in
          (Let (nn, rewrite_term_var_var t1 x y, rewrite_term_var_var t2 x y))
    | Lambda (s, t1, t2) ->
        let nn = (
          if (s = x) then y else s
        ) in
          (Lambda (nn, rewrite_term_var_var t1 x y, rewrite_term_var_var t2 x y))
    | Forall (s, t1, t2) ->
        let nn = (
          if (s = x) then y else s
        ) in
          (Forall (nn, rewrite_term_var_var t1 x y, rewrite_term_var_var t2 x y))
    | Phi (s, largs, ty, decargs, body) ->
        let nn = (
          if (s = x) then y else s
        ) in
          Phi (nn, rewrite_listvarterm_var_var largs x y, rewrite_term_var_var ty x y, decargs, rewrite_term_var_var body x y)
    | Ind (s, largs, ty, lcons) ->
        let nn = (
          if (s = x) then y else s
        ) in
          Ind (nn, rewrite_listvarterm_var_var largs x y, rewrite_term_var_var ty x y, rewrite_listterm_var_var lcons x y)
    | App (t1, t2) ->
        App (rewrite_term_var_var t1 x y, rewrite_listterm_var_var t2 x y)
    | Match (t1, l, t2, ind) ->
        Match (rewrite_term_var_var t1 x y, rewrite_listterm_var_var l x y, 
               (match t2 with
                 | None -> None
                 | Some t2 ->
                     Some (rewrite_term_var_var t2 x y))
              , (match ind with
                 | None -> None
                 | Some ind ->
                     Some (rewrite_term_var_var ind x y))
	      )
    | Cons (n, l) -> Cons (n, rewrite_term_var_var l x y)
    | Type -> Type
    | AdvMatch (t, ldes, ty) ->
	let t = rewrite_term_var_var t x y in
	let ty = (
	  match ty with
	    | None -> None
	    | Some ty -> Some (rewrite_term_var_var ty x y)
	) in
	let ldes = rewrite_listtermterm_var_var ldes x y in
	  AdvMatch (t, ldes, ty)
	  
and rewrite_listterm_var_var l x y =
  match l with
    | [] -> []
    | hd :: tl ->
        (rewrite_term_var_var hd x y) :: (rewrite_listterm_var_var tl x y)
and rewrite_listvarterm_var_var l x y =
  match l with
    | [] -> []
    | (hd1, hd2) :: tl ->
        let nn = (
          if (hd1 = x) then y else hd1
        ) in
        (nn,(rewrite_term_var_var hd2 x y)) :: (rewrite_listvarterm_var_var tl x y)
and rewrite_listtermterm_var_var l x y =
  match l with
    | [] -> []
    | (hd1, hd2) :: tl ->
	let fv = term_var hd1 in
	  if (vsin x fv) then 
	    (hd1, hd2) :: (rewrite_listtermterm_var_var tl x y)
	  else
	    (hd1, rewrite_term_var_var hd2 x y) :: (rewrite_listtermterm_var_var tl x y)	
;;

(* rewriting of a constante x by a term y in the term t *)
let rec rewrite_term_name_term t x y =
  match t with
    | Avar -> Avar
    | Obj o -> Obj o
    | Cste n -> if (n=x) then y else Cste n
    | Var v -> Var v
    | Let (s, t1, t2) ->
        (Let (s, rewrite_term_name_term t1 x y, rewrite_term_name_term t2 x y))
    | Lambda (s, t1, t2) ->
        (Lambda (s, rewrite_term_name_term t1 x y, rewrite_term_name_term t2 x y))
    | Forall (s, t1, t2) ->
        (Forall (s, rewrite_term_name_term t1 x y, rewrite_term_name_term t2 x y))
    | Phi (s, largs, ty, decargs, body) ->
        Phi (s, rewrite_listvarterm_name_term largs x y, rewrite_term_name_term ty x y, decargs, rewrite_term_name_term body x y)
    | Ind (s, largs, ty, lcons) ->
        Ind (s, rewrite_listvarterm_name_term largs x y, rewrite_term_name_term ty x y, rewrite_listterm_name_term lcons x y)
    | App (t1, t2) ->
        App (rewrite_term_name_term t1 x y, rewrite_listterm_name_term t2 x y)
    | Match (t1, l, t2, ind) ->
        Match (rewrite_term_name_term t1 x y, rewrite_listterm_name_term l x y, 
               (match t2 with
                  | None -> None
                  | Some t2 -> Some (rewrite_term_name_term t2 x y)),
	       (match ind with
                  | None -> None
                  | Some ind -> Some (rewrite_term_name_term ind x y))
              )
    | Cons (n, l) -> Cons (n, rewrite_term_name_term l x y)
    | Type -> Type
    | AdvMatch (t, ldes, ty) ->
	let t = rewrite_term_name_term t x y in
	let ty = (
	  match ty with
	    | None -> None
	    | Some ty -> Some (rewrite_term_name_term ty x y)
	) in
	let ldes = rewrite_listtermterm_name_term ldes x y in
	  AdvMatch (t, ldes, ty)

and rewrite_listterm_name_term l x y =
  match l with
    | [] -> []
    | hd :: tl ->
        (rewrite_term_name_term hd x y) :: (rewrite_listterm_name_term tl x y)
and rewrite_listvarterm_name_term l x y =
  match l with
    | [] -> []
    | (hd1, hd2) :: tl ->
        (hd1,(rewrite_term_name_term hd2 x y)) :: (rewrite_listvarterm_name_term tl x y)
and rewrite_listtermterm_name_term l x y =
  match l with
    | [] -> []
    | (hd1, hd2) :: tl ->
	(rewrite_term_name_term hd1 x y, rewrite_term_name_term hd2 x y) :: (rewrite_listtermterm_name_term tl x y)
;;

(* rewriting of a variable x by a term y in the term t (quantifier sensible) *)
let rec rewrite_term_var_term t x y =
  match t with
    | Avar -> Avar
    | Obj o -> Obj o
    | Cste n -> Cste n
    | Var v -> 
        if (v = x) then y else (Var v)
    | Let (s, t1, t2) ->
        if (s = x) then
          (Let (s, rewrite_term_var_term t1 x y, t2)) 
        else
          (Let (s, rewrite_term_var_term t1 x y, rewrite_term_var_term t2 x y))
    | Lambda (s, t1, t2) ->
        if (s = x) then
          (Lambda (s, rewrite_term_var_term t1 x y, t2)) 
        else
          (Lambda (s, rewrite_term_var_term t1 x y, rewrite_term_var_term t2 x y))
    | Forall (s, t1, t2) ->
        if (s = x) then
          (Forall (s, rewrite_term_var_term t1 x y, t2)) 
        else
          (Forall (s, rewrite_term_var_term t1 x y, rewrite_term_var_term t2 x y))
    | Phi (s, largs, ty, decargs, body) ->
        if (s = x) then
          Phi (s, 
              
              rewrite_listvarterm_var_term largs x y,
              
              (if (VarSet.subset (VarSet.singleton x) (listvarterm2varset largs)) then 
                ty 
                else (rewrite_term_var_term ty x y)),
              
              decargs,
          
              body 
          )
        else
          Phi (s, 
              
              rewrite_listvarterm_var_term largs x y,
              
              (if (VarSet.subset (VarSet.singleton x) (listvarterm2varset largs)) then 
                ty 
                else (rewrite_term_var_term ty x y)),
              
              decargs,
              
              (if (VarSet.subset (VarSet.singleton x) (listvarterm2varset largs)) then 
                body
                else (rewrite_term_var_term body x y))
          )

    | Ind (s, largs, ty, lcons) ->
        if (s = x) then
          Ind (s, 
              rewrite_listvarterm_var_term largs x y,
              (if (VarSet.subset (VarSet.singleton x) (listvarterm2varset largs)) then 
                ty 
                 else (rewrite_term_var_term ty x y)),
              lcons              
          )
        else
          Ind (s, 
              rewrite_listvarterm_var_term largs x y,
              (if (VarSet.subset (VarSet.singleton x) (listvarterm2varset largs)) then 
                ty 
                 else (rewrite_term_var_term ty x y)),
              (if (VarSet.subset (VarSet.singleton x) (listvarterm2varset largs)) then 
                lcons
              else (rewrite_listterm_var_term lcons x y))
          )
    | App (t1, t2) ->
        App (rewrite_term_var_term t1 x y, rewrite_listterm_var_term t2 x y)
    | Match (t1, l, t2, ind) ->
        Match (rewrite_term_var_term t1 x y, rewrite_listterm_var_term l x y, 
               (match t2 with
                  | None -> None
                  | Some t2 -> Some (rewrite_term_var_term t2 x y)
	       ),
	       (match ind with
                  | None -> None
                  | Some ind -> Some (rewrite_term_var_term ind x y)
	       )
        )
    | Cons (n, l) ->
        Cons (n, rewrite_term_var_term l x y)
    | Type -> Type
    | AdvMatch (t, ldes, ty) ->
	let t = rewrite_term_var_term t x y in
	let ty = (
	  match ty with
	    | None -> None
	    | Some ty -> Some (rewrite_term_var_term ty x y)
	) in
	let ldes = rewrite_listtermterm_var_term ldes x y in
	  AdvMatch (t, ldes, ty)

and rewrite_listterm_var_term l x y =
  match l with
    | [] -> []
    | hd :: tl ->
        (rewrite_term_var_term hd x y) :: (rewrite_listterm_var_term tl x y)
and rewrite_listvarterm_var_term l x y =
  match l with
    | [] -> []
    | (hd1, hd2) :: tl ->
        if (x = hd1) then
          ((hd1,rewrite_term_var_term hd2 x y)) :: tl
        else
          ((hd1,rewrite_term_var_term hd2 x y)) :: (rewrite_listvarterm_var_term tl x y)
and rewrite_listtermterm_var_term l x y =
  match l with
    | [] -> []
    | (hd1, hd2) :: tl ->
	let hd1 = rewrite_term_var_term hd1 x y in
	let fv = term_var hd1 in
	  if (vsin x fv) then 
	    (hd1, hd2) :: (rewrite_listtermterm_var_term tl x y)
	  else
	    (hd1, rewrite_term_var_term hd2 x y) :: (rewrite_listtermterm_var_term tl x y)	
;;

let rec rewrite_term_list_var_term t l =
  match l with
    | [] -> t
    | (x,y) :: tl ->
        rewrite_term_list_var_term (rewrite_term_var_term t x y) tl
;;

let rec rewrite_list_term_list_var_term lt lr =
  match lt with
    | [] -> []
    | hd :: tl ->
        (rewrite_term_list_var_term hd lr) :: (rewrite_list_term_list_var_term tl lr)
;;

let rec listrewrite_term_var_term t l =
  match l with
    | [] -> t
    | (hd1, hd2) :: tl ->
        listrewrite_term_var_term (rewrite_term_var_term t hd1 hd2) tl
;;

(* substitution *)

let rec apply_subs_var x s =
  match s with
    | [] -> Var x
    | (v, t) :: tl ->
        if (x = v) then t else apply_subs_var x tl;;

let rec apply_subs_term t s bv =
  match t with
    | Avar -> Avar
    | Obj o -> Obj o
    | Cste n -> Cste n
    | Var x -> 
        if (VarSet.subset (VarSet.singleton x) bv) then (Var x) else (apply_subs_var x s)
    | Let (x, t1, t2) ->
        Let (x, (apply_subs_term t1 s bv), (apply_subs_term t2 s (x ++ bv)))
    | Lambda (x, t1, t2) ->
        Lambda (x, (apply_subs_term t1 s bv), (apply_subs_term t2 s (x ++ bv)))
    | Forall (x, t1, t2) ->
        Forall (x, (apply_subs_term t1 s bv), (apply_subs_term t2 s (x ++ bv)))
    | Phi (x, t1, t2, t3, t4) ->
        Phi (x, 
            apply_subs_listvarterm t1 s bv, 
            apply_subs_term t2 s (bv +++ (listvarterm2varset t1)),
            t3,
            apply_subs_term t4 s (x ++ (bv +++ (listvarterm2varset t1)))
        )
                                 
    | Ind (x, t1, t2, t3) ->
        Ind (x, 
            apply_subs_listvarterm t1 s bv, 
            apply_subs_term t2 s (bv +++ (listvarterm2varset t1)),
            apply_subs_listterm t3 s (x ++ (bv +++ (listvarterm2varset t1)))
        )
    | App (t1, t2) ->
        App ((apply_subs_term t1 s bv), (apply_subs_listterm t2 s bv))
    | Match (t1, l1, t2, ind) ->
        Match ((apply_subs_term t1 s bv), (apply_subs_listterm l1 s bv),
               (match t2 with
                  | None -> None
                  | Some t2 -> Some (apply_subs_term t2 s bv)
	       ),
	       (match ind with
                  | None -> None
                  | Some ind -> Some (apply_subs_term ind s bv)
	       )
        )
    | Cons (n, l1) ->
        Cons (n, (apply_subs_term l1 s bv))
    | Type -> Type
    | AdvMatch (t, ldes, ty) ->
	let t = apply_subs_term t s bv in
	let ty = (
	  match ty with
	    | None -> None
	    | Some ty -> Some (apply_subs_term ty s bv)
	) in
	let ldes = apply_subs_listtermterm ldes s bv in
	  AdvMatch (t, ldes, ty)
and apply_subs_listterm l s bv =
  match l with
    | [] -> []
    | hd :: tl ->
        (apply_subs_term hd s bv)::(apply_subs_listterm tl s bv)
and apply_subs_listvarterm l s bv =
  match l with
    | [] -> []
    | (hd1, hd2) :: tl ->
        (hd1,(apply_subs_term hd2 s bv))::(apply_subs_listvarterm tl s (hd1 ++ bv))
and apply_subs_listtermterm l s bv =
  match l with
    | [] -> []
    | (hd1, hd2) :: tl ->
	(hd1, apply_subs_term hd2 s ((term_var hd1) +++ bv)) :: (apply_subs_listtermterm tl s bv)
;;

let rec apply_subs_listoptionterm l s bv =
  match l with
    | [] -> []
    | None :: tl ->
        None :: (apply_subs_listoptionterm tl s bv)
    | (Some hd)::tl ->
        (Some (apply_subs_term hd s bv)) :: (apply_subs_listoptionterm tl s bv)

let rec apply_subs_subs_rev x t s = 
  match s with
    | [] -> []
    | (x', t') :: tl ->
        (x', apply_subs_term t' ((x,t) :: []) VarSet.empty) :: (apply_subs_subs_rev x t tl);;

let rec comp_subs_rev s =
  match s with
    | [] -> []
    | (x, t) :: tl ->
        (x, t) :: comp_subs_rev (apply_subs_subs_rev x t tl);;

let comp_subs s = rev (comp_subs_rev (rev s));;

let rec apply_subs_context c s sv =
  match c with
    | [] -> []
    | (hd1, hd2) :: tl ->
        (hd1, apply_subs_term hd2 s sv) :: (apply_subs_context tl s (sv))
;;

let rec apply_subs_listcontext c s sv =
  match c with
    | [] -> []
    | hd :: tl ->
        (apply_subs_context hd s sv) :: (apply_subs_listcontext tl s sv)
;;

let rec var2cste t l =
  let l = VarSet.elements l in
    List.fold_left (
      fun t hd ->
        (rewrite_term_var_term t hd (Cste hd))
    ) t l
;;

let rec var2cste_listvarterm lt l =
  match lt with
    | [] -> []
    | (hd1, hd2) :: tl ->
        (hd1, (var2cste hd2 l)) :: (var2cste_listvarterm tl l)
;;

let rec var2cste_listterm lt l =
  match lt with
    | [] -> []
    | hd :: tl ->
        (var2cste hd l) :: (var2cste_listterm tl l)
;;

(*
let rec var2cste_implicite t l impl =
  let l = VarSet.elements l in
    List.fold_left (
      fun t hd ->
        (rewrite_term_var_term t hd (App (Cste hd, 
					 
					 list_of_n_elt (Var "?T")
					   (
					     try 
					       VarMap.find hd impl
					     with
					       | _ -> 0
					   )
					   
					 )
				    )
	)
    ) t l
;;
*)

let var2cste_implicite t def overload impl =
  let fv = term_var t in
  let rewritelist = 
    VarSet.fold (
      fun elt l ->
	match finddef elt def with
	  | None -> (
	      try 
		let _ = VarMap.find elt overload in
		  (elt, Cste elt)::l
	      with
		| _ -> l
	    )
	  | Some (n, (te, ty, nat)) -> (
	      (elt, (App (Cste n, 					 
			  list_of_n_elt Avar
			    (
			      try 
				VarMap.find n impl
			      with
				| _ -> 0
			    )
			 )
		    )
	      )::l
	    )
    ) fv [] in
    rewrite_term_list_var_term t rewritelist
;;


let rec var2cste_listvarterm_implicite lt l impl =
  match lt with
    | [] -> []
    | (hd1, hd2) :: tl ->
        (hd1, (var2cste_implicite hd2 l impl)) :: (var2cste_listvarterm_implicite tl l impl)
;;

let rec var2cste_listterm_implicite lt l impl =
  match lt with
    | [] -> []
    | hd :: tl ->
        (var2cste_implicite hd l impl) :: (var2cste_listterm_implicite tl l impl)
;;


(* def should be only composed of ground term, else the function may never return *)
let rec rewrite_mutual_def t def =
  let t' = rewrite_term_list_var_term t def in
    if (t = t') then
      t 
    else
      rewrite_mutual_def t' def
;;
