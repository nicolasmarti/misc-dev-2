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
open Definition;;

let rec term_var t =
  match t with
    | Avar -> VarSet.empty
    | Obj o -> VarSet.empty
    | Cste n -> VarSet.empty
    | Var v -> 
         (VarSet.singleton v)
    | Let (x, t1, t2) ->
	x ++ ((term_var t1) +++ (term_var t2 ))
    | Lambda (s, t1, t2) ->
        s ++ ((term_var t1) +++ (term_var t2 ))
    | Forall (s, t1, t2) ->
        s ++ ((term_var t1) +++ (term_var t2 ))
    | Phi (s, t1, t2, l, t4) ->
        s ++ ((listvarterm_var t1) +++ (term_var t2) +++ (term_var t4))
    | Ind (s, t1, t2, t3) ->
        s ++ ((listvarterm_var t1) +++ (term_var t2) +++ (listterm_var t3))
    | App (t1, t2) ->
        (term_var t1) +++ (listterm_var t2)
    | Match (t1, l, ty, ind) ->
        (term_var t1) +++ (listterm_var l) +++ (
          match ty with
            | None -> VarSet.empty
            | Some ty -> term_var ty
        ) +++ (
          match ind with
            | None -> VarSet.empty
            | Some ind -> term_var ind
        )
    | Cons (n, t1) ->
        (term_var t1)
    | Type -> VarSet.empty
    | AdvMatch (t, ldes, ty) ->
	(term_var t) +++ (listtermterm_var ldes) +++ (
          match ty with
            | None -> VarSet.empty
            | Some ty -> term_var ty
        ) 
and listterm_var lt =
  match lt with
    | [] -> VarSet.empty
    | hd :: tl ->
        (term_var hd) +++ (listterm_var tl)
and listvarterm_var ctxt =
  match ctxt with
    | [] -> VarSet.empty
    | (hd1, hd2) :: tl ->
        hd1 ++ (listvarterm_var tl) +++ (term_var hd2)
and listtermterm_var l =
  match l with
    | [] -> VarSet.empty
    | (hd1,hd2)::tl ->
	(term_var hd1) +++ (term_var hd2) +++ listtermterm_var tl
;;

let rec listvarterm2varset ctxt =
  match ctxt with
    | [] -> VarSet.empty
    | (hd1,hd2) :: tl ->
        hd1 ++ (listvarterm2varset tl)
;;

let rec term_fv t bv =
  match t with
    | Avar -> VarSet.empty
    | Obj o -> VarSet.empty
    | Cste n -> VarSet.empty
    | Var v -> 
        if (VarSet.subset (VarSet.singleton v) bv) then VarSet.empty else (VarSet.singleton v)
    | Let (s, t1, t2) ->
        ((term_fv t1 bv) +++ (term_fv t2 (s ++ bv)))
    | Lambda (s, t1, t2) ->
        ((term_fv t1 bv) +++ (term_fv t2 (s ++ bv)))
    | Forall (s, t1, t2) ->
        ((term_fv t1 bv) +++ (term_fv t2 (s ++ bv)))
    | Phi (s, t1, t2, l, t4) ->
        ((listvarterm_fv t1 bv) +++ (term_fv t2 (bv +++ (listvarterm2varset t1))) +++ (term_fv t4 (s ++ (bv +++ (listvarterm2varset t1)))))
    | Ind (s, t1, t2, t3) ->
        ((listvarterm_fv t1 bv) +++ (term_fv t2 (bv +++ (listvarterm2varset t1))) +++ (listterm_fv t3 (s ++ (bv +++ (listvarterm2varset t1)))))
    | App (t1, t2) ->
        (term_fv t1 bv) +++ (listterm_fv t2 bv)
    | Match (t1, l, ty, ind) ->
        (term_fv t1 bv) +++ (listterm_fv l bv) +++ (
          match ty with
            | None -> VarSet.empty
            | Some ty -> term_fv ty bv
        ) +++ (
          match ind with
            | None -> VarSet.empty
            | Some ind -> term_fv ind bv
        )
    | Cons (n, t1) ->
        (term_fv t1 bv)
    | Type -> VarSet.empty
    | AdvMatch (t, ldes, ty) ->
	(term_fv t bv) +++ (listtermterm_fv ldes bv) +++ (
          match ty with
            | None -> VarSet.empty
            | Some ty -> term_fv ty bv
        )
and listterm_fv lt bv =
  match lt with
    | [] -> VarSet.empty
    | hd :: tl ->
        (term_fv hd bv) +++ (listterm_fv tl bv)
and listvarterm_fv ctxt bv =
  match ctxt with
    | [] -> VarSet.empty
    | (hd1, hd2) :: tl ->
        (term_fv hd2 bv) +++ (listvarterm_fv tl (hd1 ++ bv))
and listtermterm_fv l bv =
  match l with
    | [] -> VarSet.empty
    | (hd1, hd2)::tl ->
	(term_fv hd2 (bv +++ (term_var hd1))) +++ (listtermterm_fv tl bv)
;;

let rec term_cons t =
  match t with
    | Avar -> VarSet.empty 
    | Obj o -> VarSet.empty
    | Cste n -> VarSet.singleton n
    | Var v -> 
        VarSet.empty
    | Let (s, t1, t2) ->
        ((term_cons t1) +++ (term_cons t2))
    | Lambda (s, t1, t2) ->
        ((term_cons t1) +++ (term_cons t2))
    | Forall (s, t1, t2) ->
        ((term_cons t1) +++ (term_cons t2))
    | Phi (s, t1, t2, l, t4) ->
        ((listvarterm_cons t1) +++ (term_cons t2) +++ (term_cons t4))
    | Ind (s, t1, t2, t3) ->
        ((listvarterm_cons t1) +++ (term_cons t2) +++ (listterm_cons t3))
    | App (t1, t2) ->
        (term_cons t1) +++ (listterm_cons t2)
    | Match (t1, l, t2, ind) ->
        (term_cons t1) +++ (listterm_cons l) +++ (

          match t2 with
            | None -> VarSet.empty
            | Some t2 -> term_cons t2

        ) +++ (

          match ind with
            | None -> VarSet.empty
            | Some ind -> term_cons ind

        )
    | Cons (n, t1) ->
        (term_cons t1)
    | Type -> VarSet.empty
    | AdvMatch (t, ldes, ty) ->
	(term_cons t) +++ (listtermterm_cons ldes) +++ (
          match ty with
            | None -> VarSet.empty
            | Some ty -> term_cons ty
        )
and listterm_cons lt =
  match lt with
    | [] -> VarSet.empty
    | hd :: tl ->
        (term_cons hd) +++ (listterm_cons tl)
and listvarterm_cons ctxt =
  match ctxt with
    | [] -> VarSet.empty
    | (hd1, hd2) :: tl ->
        (term_cons hd2) +++ (listvarterm_cons tl)
and listtermterm_cons l =
  match l with
    | [] -> VarSet.empty
    | (hd1, hd2) :: tl ->
        (term_cons hd1) +++ (term_cons hd2) +++ (listtermterm_cons tl)
;;

let rec listvarterm2varset l =
  match l with
    | [] -> VarSet.empty
    | (hd1, hd2) :: tl ->
        hd1 ++ (listvarterm2varset tl)
;;


let rec app_nf t =
  match t with
    | App (t1, t2) -> (
        match t1 with
          | App (t11, t12) ->
              app_nf (App (t11, t12@t2))
          | _ ->
              match t2 with
                | [] -> t1
                | _ -> t
      )
    | _ -> t
;;

let app_nf_listterm lt =

  List.map (

    fun hd ->
      app_nf hd

  ) lt
;;


let rec largs_lambdas t la =
  match la with
    | [] -> t
    | (hd1, hd2) :: tl ->
        Lambda (hd1, hd2, largs_lambdas t tl)
;;

let rec largs_lambdas_listterm lt ta =
  match lt with
    | [] -> []
    | hd :: tl ->
        (largs_lambdas hd ta) :: (largs_lambdas_listterm tl ta)
;;

let decomp_app t =
  let t' = app_nf t in
    match t' with
      | App (fct, args) ->
          (fct, args)
      | _ -> (t, [])
;;

let rec largs_foralls t la =
  match la with
    | [] -> t
    | (hd1, hd2) :: tl ->
        Forall (hd1, hd2, largs_foralls t tl)
;;

let rec largs_foralls_listterm lt la =
  match lt with
    | [] -> []
    | hd :: tl ->
        (largs_foralls hd la) :: (largs_foralls_listterm tl la)
;;

let rec listapp_fct l =
  match l with
    | [] -> []
    | hd :: tl ->
        let (fct, _) = decomp_app hd in
          fct :: listapp_fct tl
;;

let rec decomp_foralls t =
  match t with
    | Forall (x, t11, t12) ->
        let (t1, t2) = decomp_foralls t12 in
          ((x,t11)::t1, t2)
    | _ -> ([], t)
;;

let rec decomp_lambdas t =
  match t with
    | Lambda (x, t11, t12) ->
        let (t1, t2) = decomp_lambdas t12 in
          ((x,t11)::t1, t2)
    | _ -> ([], t)
;;

let rec decomp_nlambdas t n =
  match n with
    | 0 -> ([], t)
    | _ ->
        match t with
          | Lambda (x, t11, t12) ->
              let (t1, t2) = decomp_nlambdas t12 (n - 1) in
                ((x,t11)::t1, t2)
          | _ -> ([], t)
;;

let rec list_name2list_var l =
  match l with 
    | [] -> []
    | hd :: tl ->
        Var hd :: (list_name2list_var tl)
;;

let rec term_diff t bv fv =
  match t with
    | Avar -> Avar
    | Type -> Type
    | Obj o -> Obj o
    | Cste n -> Cste n
    | Var v -> 
        if not (vsin v bv) then (
          let x = fresh_name_list_name (bv +++ fv) v in
            Var x
        ) else
          Var v

    | Let (s, t1, t2) ->
        let t1 = term_diff t1 bv fv in
        let fv = fv +++ (term_fv t1 bv) in
        let t2 = term_diff t2 (s ++ bv) fv in
          Let (s, t1, t2)

    | Lambda (s, t1, t2) ->
        let t1 = term_diff t1 bv fv in
        let fv = fv +++ (term_fv t1 bv) in
        let t2 = term_diff t2 (s ++ bv) fv in
          Lambda (s, t1, t2)

    | Forall (s, t1, t2) ->
        let t1 = term_diff t1 bv fv in
        let fv = fv +++ (term_fv t1 bv) in
        let t2 = term_diff t2 (s ++ bv) fv in
          Forall (s, t1, t2)

    | Phi (s, t1, t2, l, t4) ->
        let t1 = listvarterm_diff t1 bv fv in
        let bv = bv +++ (listvarterm2varset t1) in
        let fv = fv +++ (listvarterm_fv t1 bv) in
        let t2 = term_diff t2 bv fv in
        let fv = fv +++ (term_fv t2 bv) in
        let bv = s ++ bv in
        let t4 = term_diff t4 bv fv in
          Phi (s, t1, t2, l, t4)

    | Ind (s, t1, t2, t3) ->
        let t1 = listvarterm_diff t1 bv fv in
        let bv = bv +++ (listvarterm2varset t1) in
        let fv = fv +++ (listvarterm_fv t1 bv) in
        let t2 = term_diff t2 bv fv in
        let fv = fv +++ (term_fv t2 bv) in
        let bv = s ++ bv in
        let t3 = listterm_diff t3 bv fv in
          Ind (s, t1, t2, t3)

    | App (t1, t2) ->
        let t1 = term_diff t1 bv fv in
        let fv = fv +++ (term_fv t1 bv) in
        let t2 = listterm_diff t2 bv fv in
          App (t1, t2)

    | Match (t1, l, ty, ind) ->
        let t1 = term_diff t1 bv fv in
        let fv = fv +++ (term_fv t1 bv) in
        let l = listterm_diff l bv fv in
        let fv = fv +++ (listterm_fv l bv) in
        let (ty, _) = (
          match ty with
            | None -> (None, fv)
            | Some ty ->
                let fv = fv +++ (term_fv ty bv) in
                  (Some (term_diff ty bv fv), fv)
        ) in        
        let (ind, _) = (
          match ind with
            | None -> (None, fv)
            | Some ind ->
                let fv = fv +++ (term_fv ind bv) in
                  (Some (term_diff ind bv fv), fv)
        ) in        	  
          Match (t1, l, ty, ind)
            
    | Cons (n, t1) ->
        let t1 = term_diff t1 bv fv in
          Cons (n, t1)
	    
    | AdvMatch (t, ldes, ty) ->
	let t = term_diff t bv fv in
        let fv = fv +++ (term_fv t bv) in
        let ldes = listtermterm_diff ldes bv fv in
        let ty = (
          match ty with
            | None -> None
            | Some ty ->
                let fv = fv +++ (listtermterm_fv ldes bv) in
                  Some (term_diff ty bv fv)
        ) in        
          AdvMatch (t, ldes, ty)

and listterm_diff l bv fv =
  match l with
    | [] -> []
    | hd :: tl ->
        let hd = term_diff hd bv fv in
        let fv = fv +++ (term_fv hd bv) in
          hd :: (listterm_diff tl bv fv)

and listvarterm_diff l bv fv =
  match l with
    | [] -> []
    | (hd1, hd2) :: tl ->
        let hd2 = term_diff hd2 bv fv in
        let fv = fv +++ (term_fv hd2 bv) in
          (hd1, hd2) :: (listvarterm_diff tl (hd1 ++ bv) fv)

and listtermterm_diff l bv fv =
  match l with
    | [] -> []
    | (hd1, hd2) :: tl ->
	let hd1fv = term_var hd1 in
	let hd2 = term_diff hd2 (bv +++ hd1fv) fv in
	let fv = fv +++ (term_fv hd2 (bv +++ hd1fv)) in
	  (hd1, hd2) :: (listtermterm_diff tl bv fv)

;;

let rec term_size_int t =
  match t with      
    | Obj o -> 1
    | Cste n -> 1
    | Var v -> 
        1
    | Let (s, t1, t2) ->
        1 + term_size_int t1 + term_size_int t2
    | Lambda (s, t1, t2) ->
        1 + term_size_int t1 + term_size_int t2
    | Forall (s, t1, t2) ->
        1 + term_size_int t1 + term_size_int t2
    | Phi (s, t1, t2, l, t4) ->
        1 + listvarterm_size_int t1 + term_size_int t2 + term_size_int t4
    | Ind (s, t1, t2, t3) ->
	1 + listvarterm_size_int t1 + term_size_int t2 + listterm_size_int t3
    | App (t1, t2) ->
        1 + term_size_int t1 + listterm_size_int t2
    | Match (t1, l, ty, ind) ->
	1 + term_size_int t1 + listterm_size_int l
    | Cons (n, t1) ->
        1 + term_size_int t1
    | Type -> 1
	
    (* here remains only AdvMatch, but this function should be for typechecked terms .... exception ???*) 
    | _ -> 0 
and listterm_size_int lt =
  match lt with
    | [] -> 0
    | hd :: tl ->
        term_size_int hd + listterm_size_int tl
and listvarterm_size_int ctxt =
  match ctxt with
    | [] -> 0
    | (hd1, hd2) :: tl ->
        1 + term_size_int hd2 + listvarterm_size_int tl
;;

(* here the term should be typed *)
let rec term_nature t def =
  match t with
    | Avar -> UNKNOWN
    | Obj o -> UNKNOWN
    | Cste c -> (
	
	match finddef c def with
	  | None -> UNKNOWN
	  | Some (n , (te, ty, nature)) -> 
	      nature

      )
    | Var v -> 
         UNKNOWN
    | Let (x, t1, t2) ->
	term_nature t2 def
    | Lambda (s, t1, t2) ->
        FUNCTION
    | Forall (s, t1, t2) ->
        TYPE
    | Phi (s, t1, t2, l, t4) ->
        FUNCTION
    | Ind (s, t1, t2, t3) ->
        TYPE
    | App (t1, t2) -> (
	match term_nature t1 def with
	  | DATA -> DATA
	  | _ -> UNKNOWN
      )        
    | Match (t1, l, ty, ind) ->
	UNKNOWN
    | Cons (n, t1) ->
        DATA
    | Type -> TYPE
    | AdvMatch (t, ldes, ty) ->
	UNKNOWN
;;

let rec term_varfct t def =
  match t with
    | App (Var v, largs) ->
	VarSet.singleton v 
	  
    | App (f, largs) ->
	(term_varfct f def) 

    | Cste c -> (
	
	match term_nature t def with
	  | DATA -> VarSet.empty
	  | _ -> VarSet.singleton "maybe"

      )
    | _ -> VarSet.empty
;;
