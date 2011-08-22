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
open Lexing;;
open List;;
open String;;

open Def;;
open Printer;;
open Freshness;;
open Term;;
open Alpha;;
open Beta;;
open Termeq;;
open Varset;;
open Varmap;;
open Arith;;
open Rewrite;;
open Fold;;
open Unfold;;
open Listext;;
open Indprinc;;
open Unification;;
open Unfoldbetared;;
open Simpl;;
open Termchecker;;
open Kernel;;
open Definition;;

type tactics =
    | Equiv of term
    | IntroAs of string
    | Intro
    | Apply of term
    | Generalize of term * string
    | Simpl
    | SimplIn of string
    | Factorize of term list
    | Destruct of term
    | Exact of term
    | Idtac
    | Fail
    | TacticSeq of tactics * tactics
    | Repeat of tactics
    | Dotactic of int * tactics
    | Trytactic of tactics
    | Partactic of tactics list
    | Ortactic of tactics list
    | Oracle of string
;;

let rec string_of_tactic t implicite =
  match t with
    | Equiv t -> 
        concat "" ("equiv " :: (string_of_term t implicite) :: [])
    | Exact t ->
        concat "" ("exact " :: (string_of_term t implicite) :: [])
    | Intro -> 
        "intro"
    | IntroAs t ->
        concat "" ("intro " :: t :: [])
    | Apply t ->
        concat "" ("apply " :: (string_of_term t implicite) :: [])
    | Generalize (t, s) ->
        concat "" ("generalize " :: (string_of_term t implicite) :: " as " :: s :: [])
    | Simpl ->
        "simpl"
    | SimplIn s ->
        concat "" ("simpl in " :: s :: [])
    | Factorize t ->
        concat "" ("factorize " :: (string_of_listterm t implicite) :: [])        
    | Destruct t ->
        concat "" ("destruct " :: (string_of_term t implicite) :: [])        
    | Fail ->
        "fail"
    | Idtac -> 
        "idtac"
    | TacticSeq (t1, t2) ->
        concat "" ((string_of_tactic t1 implicite) :: "; " :: (string_of_tactic t2 implicite) :: [])        
    | Dotactic (n2, t) ->
        concat "" ("do " :: (string_of_int n2) :: " " :: (string_of_tactic t implicite) :: ")" :: [])        
    | Repeat t ->
        concat "" ("(repeat " :: (string_of_tactic t implicite) :: ")" :: [])
    | Trytactic t ->
        concat "" ("(try " :: (string_of_tactic t implicite) :: ")" :: [])
    | Partactic l ->
        concat "" ("[ " :: (string_of_partactic l implicite) :: " ]" :: [])
    | Ortactic l ->
        concat "" ("[ " :: (string_of_ortactic l implicite) :: " ]" :: [])
    | Oracle t ->
        concat "" ("oracle " :: t :: [])
and string_of_partactic l implicite =
  match l with
    | [] -> ""
    | hd :: tl ->
        concat "" ((string_of_tactic hd implicite) :: " | " :: (string_of_partactic tl implicite) :: []) 
and string_of_ortactic l implicite =
  match l with
    | [] -> ""
    | hd :: tl ->
        concat "" ((string_of_tactic hd implicite) :: " || " :: (string_of_partactic tl implicite) :: [])   
and string_of_listtactic l implicite =
  match l with
    | [] -> ""
    | hd :: tl ->
        concat "" ((string_of_tactic hd implicite) :: ".\n" :: (string_of_listtactic tl implicite) :: [])
;;  


(* useful function *)
(************************)

let rec listconstructors2def l n name =
  match l with 
    | [] -> []
    | (hd1, hd2) :: tl ->
        (hd1, Cons (n,Cste (name)))::(listconstructors2def tl (n+1) name);;

let rec append_foralls_constructors lc ll =
  match lc with
    | [] -> []
    | (hd1, hd2) :: tl ->
        (hd1, largs_foralls hd2 ll) :: (append_foralls_constructors tl ll);;

let rec fold_constructors lc def =
  match lc with 
    | [] -> []
    | (hd1, hd2) :: tl ->
        (hd1, fold hd2 VarSet.empty def) :: (fold_constructors tl def)
;;

let rec rewrite_subgoal_var_term sg x t =
  match sg with 
    | [] -> []
    | (ctxt, sgn, sgt) :: tl ->
        (ctxt, sgn, rewrite_term_var_term sgt x t) :: (rewrite_subgoal_var_term tl x t);;

let rec var_type_in_context x ctxt =
  match ctxt with
    | [] -> None
    | (hd1, hd2)::tl ->
        if (hd1 = x) then Some hd2 else var_type_in_context x tl;;

let rec apply_modifie_state' t q s ctxt sv def =
  match q with
    | [] -> ([],t)
    | (hd1, hd2) :: tl ->
        match (var_type_in_context hd1 s) with
          | None -> (
              let x = (fresh_name_list_name sv "subgoal0") in 
              let (c, te) = (apply_modifie_state' (App(t,Var x ::[])) tl s ctxt (x ++ sv) def) in
                ((ctxt,x,(fold hd2 sv def)):: (rewrite_subgoal_var_term c hd1 (Var x)) , te)
            )
          | Some te ->
              apply_modifie_state' (App(t,te::[])) tl s ctxt sv def;;


let apply_modifie_state t q s hd1 hd2 hd3 tl ln te ty def =
  let (nsg, pt) = (apply_modifie_state' t q s hd1 (term_var te) def) in          
  let te2 = (rewrite_term_var_term te hd2 pt) in (
    (nsg @ tl, (ln, te2, ty), List.length q - List.length s)
  );;

let rec simpl_ctxt c x def =
  match c with 
    | [] -> []
    | (hd1, hd2) :: tl ->
        if (hd1 = x) then (hd1,fold (simpl hd2 def) VarSet.empty def) :: tl else
          (hd1, hd2) :: (simpl_ctxt tl x def);;

(*************************************)

(* equivalence *)

let equiv_tactic t lg def coercion oracles overload implicite =

  match lg with
    | ((hd1,hd2,hd3)::tl,g) -> (
        match check_term_wctxt "" hd1 t (Some Type) def coercion (varmap_vallist oracles) overload implicite with
          | None -> None
          | Some (te, ty) ->
              if (term_eq te hd3 def) then (      
                Some ((hd1,hd2,t)::tl,g,1)            
              ) else (          
                None
              )
      )
    | _ -> None
;;           

(* intro *)

let intro_tactic x lg def coercion oracles overload implicite =
  match lg with
    | ((hd1,hd2,Forall (v,t,hd3))::tl,(ln,te,ty)) ->  (

        let x2 = (fresh_name_list_name (listvarterm2varset hd1) x) in (
          Some (((x2,t)::hd1,hd2,(rewrite_term_var_term (alpha_term_vars hd3 (x2 ++ (listvarterm2varset hd1))) v (Var x2)))::tl,
               (ln,rewrite_term_var_term te hd2 (Lambda (x2,t,(Var hd2))),ty), 1)
        )
                                                                                             
      );
    | ((hd1,hd2,hd3)::tl,(ln,te,ty)) ->  (
        
        let hd3' = unfold_simpl hd3 def in
          match hd3' with
            | Forall (v, t1, t2) ->

                let t1' = fold t1 VarSet.empty def in
                let t2' = fold t2 VarSet.empty def in
                let x2 = (fresh_name_list_name (listvarterm2varset hd1) x) in (
                  Some (((x2,t1')::hd1,hd2,(rewrite_term_var_term (alpha_term_vars t2' (x2 ++ (listvarterm2varset hd1))) v (Var x2)))::tl,
                       (ln,rewrite_term_var_term te hd2 (Lambda (x2,t1',(Var hd2))),ty), 1)
                  )

            | _ ->  None
                
      )
    | _ ->  None
;;

(* exact *)

let exact_tactic t lg def coercion oracles overload implicite =
  match lg with
    | ((hd1,hd2,hd3)::tl,(ln,te,ty)) ->  (
          match check_term_wctxt "" hd1 t (Some hd3) def coercion (varmap_vallist oracles) overload implicite with
            | None -> None
            | Some (te2, ty2) ->  
                Some (rewrite_subgoal_var_term tl hd2 te2,(ln,(rewrite_term_var_term te hd2 te2),ty), 0)
      )
    | _ -> None
;;


let apply_tactic t lg def coercion oracles overload implicite =
  match lg with
    | ((hd1,hd2,hd3)::tl,(ln,te,ty)) ->  (
        let t = (unfold_simpl t def) in
          match check_term_wctxt "" hd1 t None def coercion (varmap_vallist oracles) overload implicite with
            | None -> None
            | Some (te2, ty2) ->
                let (goalv, goalc) = (decomp_foralls (unfold_simpl hd3 def)) in
                let (proofv, proofg) = (decomp_foralls (alpha_term_vars (unfold_simpl ty2 def) (listvarterm2varset hd1))) in
                  if (List.length proofv < List.length goalv) then
                    None
                  else
                    match unification_term (largs_foralls proofg (nth_tail ((List.length proofv) - (List.length goalv)) proofv)) (unfold_simpl hd3 def) VarSet.empty def with
                      | Mgu s -> (
                          
                          
                          let ty2' = apply_subs_term ty2 (comp_subs s) (listvarterm2varset hd1) in
                          let te2' = apply_subs_term te2 (comp_subs s) (listvarterm2varset hd1) in
                            
                            match check_term_wctxt "" hd1 te2' (Some (fold ty2' VarSet.empty def)) def coercion (varmap_vallist oracles) overload implicite with
                              | None -> 
                                  None
                              | Some (te3, ty3) ->
                                  if (term_eq
                                         ty2' 
                                         hd3                     
                                         def
                                  ) then (
                                    Some 
                                      (rewrite_subgoal_var_term tl hd2 te3,
                                      (ln,
                                      (
                                        rewrite_term_var_term te hd2 te3),ty
                                      ),
                                      0
                                      )
                                  ) else (                                          
                                    let (l1, l2, _) = 
                                      
                                      
                                      (apply_modifie_state te3 
                                          (rev (apply_subs_context (rev (nth_head ((List.length proofv) - (List.length goalv)) proofv)) (comp_subs s) (listvarterm2varset hd1)))
                                          (comp_subs s) hd1 hd2 hd3 tl ln te ty def)
                                    in
                                      (*Some (l1, l2, ((List.length proofv) - (List.length goalv)))*)
                                      Some (l1, l2, (List.length l1) - (List.length tl))
                                  )
                        )
                      | _ -> (
                          match unification_term (largs_foralls proofg (nth_tail ((List.length proofv) - (List.length goalv)) proofv)) hd3 VarSet.empty def with
                            | Mgu s -> (
                                let ty2' = apply_subs_term ty2 (comp_subs s) (listvarterm2varset hd1) in
                                let te2' = apply_subs_term te2 (comp_subs s) (listvarterm2varset hd1) in
                                  match check_term_wctxt "" hd1 te2' (Some (fold ty2' VarSet.empty def)) def coercion (varmap_vallist oracles) overload implicite with
                                    | None -> 
                                        None
                                    | Some (te3, ty3) ->
                                        if (term_eq
                                               ty2' 
                                               hd3                     
                                               def
                                        ) then (
                                          Some 
                                            (rewrite_subgoal_var_term tl hd2 te3,
                                            (ln,
                                            (
                                              rewrite_term_var_term te hd2 te3),ty
                                            ),
                                            0
                                            )
                                        ) else
                                          let (l1, l2, _) = 
                                            (apply_modifie_state te3 
                                                (rev (apply_subs_context (rev (nth_head ((List.length proofv) - (List.length goalv)) proofv)) (comp_subs s) (listvarterm2varset hd1)))
                                                (comp_subs s) hd1 hd2 hd3 tl ln te ty def)
                                          in
                                            (*Some (l1, l2, ((List.length proofv) - (List.length goalv)))*)
                                            Some (l1, l2, (List.length l1) - (List.length tl))
                                              
                              )
                            | NoMgu -> None
                            | DnkMgu -> None


                        )
      )
    | _ -> None
;;

(* generalize *)      

let generalize_tactic t x lg def coercion oracles overload implicite =
  match lg with
    | ((hd1,hd2,hd3)::tl,(ln,te,ty)) ->  (
          match check_term_wctxt "" hd1 t None def coercion (varmap_vallist oracles) overload implicite with
            | None -> None
            | Some (te2, ty2) -> 
                let hd3' = (Forall (x,ty2, rewrite_term_term_term hd3 te2 (Var x) VarSet.empty def)) in (
                  
                  Some ((hd1,hd2,fold hd3' VarSet.empty def)::tl,
                       (ln,fold (rewrite_term_var_term te hd2 (App(Var hd2, te2::[]))) VarSet.empty def,ty),
                       1
                  )
                )                    
      )
    | _ -> None
;;

(* simpl *)

let simpl_tactic lg def coercion oracles overload implicite =
  match lg with
    | ((hd1,hd2,hd3)::tl,(ln,te,ty)) ->  (
        Some ((hd1,hd2, fold (simpl hd3 def) VarSet.empty def)::tl,(ln,te,ty), 1)
      )
    | _ -> None
;; 

(* simpl in *)        
(* refaire une fonction d'exec  *)

let simpl_in_tactic x lg def coercion oracles overload implicite =
  match lg with
    | ((hd1,hd2,hd3)::tl,(ln,te,ty)) ->  (
        Some ((simpl_ctxt hd1 x def,hd2,hd3)::tl,(ln,te,ty), 1)
      )
    | _ -> None
;;

(* oracle *)

(* BIG PROBLEM: oracle is already given as a list ... everything to redo ? *) 
let oracle_tactic t lg def coercion oracles overload implicite =
  match lg with
    | ((hd1,hd2,hd3)::tl,(ln,te,ty)) ->  (
	try (
	  
	  let hd = VarMap.find t oracles in
	    
	    match hd hd1 hd3 def with
	      | None -> None
	      | Some proof ->
		  match check_term_wctxt "" hd1 proof (Some hd3) def coercion (varmap_vallist oracles) overload implicite with
		    | None -> None
		    | Some (te2, ty2) -> 
			Some (rewrite_subgoal_var_term tl hd2 te2,(ln,(rewrite_term_var_term te hd2 te2),ty), 0)
			              
              
	) with
	  | _ -> None
      )
    | _ -> None

;;


(* factorize *)


let rec factorize_tactic_list hd3 t x ty2 lx def =
  match (t, x) with
    | (hdt :: tlt, hdx::tlx) ->
        factorize_tactic_list (rewrite_term_term_term hd3 hdt (Var hdx) VarSet.empty def) tlt tlx ty2 lx def
    | _ ->
        let l = List.combine lx ty2 in
          largs_lambdas hd3 l
;;

let factorize_tactic t lg def coercion oracles overload implicite =
  match lg with
    | ((hd1,hd2,hd3)::tl,(ln,te,ty)) ->  (
        let x = (fresh_names ((listvarterm2varset hd1) +++ (term_var hd3)) (List.length t)) in 

          match List.fold_left (

            fun tl' hd ->

              match check_term_wctxt "" hd1 hd None def coercion (varmap_vallist oracles) overload implicite with
                | None -> None 
                | Some (te2, ty2) ->
                    match tl' with
                      | None -> None
                      | Some (lte, lty) ->
                          Some (lte @ te2::[], lty @ ty2::[])

          ) (Some ([],[])) t with

            | None -> None
            | Some (l1, lt) ->  
                Some ((hd1,hd2, App((factorize_tactic_list hd3 l1 x lt x def), l1))::tl,(ln,te,ty), 1)
      )
    | _ -> None 
;;          

(* destruct *)

let rec match_var_args x from into =
  match (from, into) with
    | ((hd11, hd12) :: tl1, (hd21, hd22) :: tl2) ->
        if (x = hd11) then hd21 else
          (match_var_args x tl1 tl2)
    | _ -> x;;

let rec match_comp_args s from into =
  match s with
    | [] -> []
    | (hd1, hd2) :: tl ->
        (match_var_args hd1 from into, hd2) :: (match_comp_args tl from into);;

let rec destruct_build n iname indargs itype ilc lc args bv ty ctxt dt def overload implicite =
  match lc with
    | [] -> ([], [], 0)
    | (hdc::tlc) -> (        
        let hdc2 = (alpha_term_vars (largs_foralls hdc indargs) ((listvarterm2varset ctxt) +++ (listterm_fv args VarSet.empty))) in
        let (fcv, con) = (decomp_foralls hdc2) in 
        let (i, iargs) = (decomp_app con) in 
          match (unification_listterm 
                   iargs
                   args
                   VarSet.empty
                   def
		) with
            | NoMgu -> 
                destruct_build (n+1) iname indargs itype ilc tlc args bv ty ctxt dt def overload implicite 
            | Mgu s ->
                let hdc3 = (alpha_term_vars hdc2 (listvarterm2varset (fcv @ ctxt))) in
                let (lvt, _) = (decomp_foralls hdc3) in 
                let s' = comp_subs (
                  
                  match (unification_listterm (list_name2list_var (list_proj1 fcv)) (list_name2list_var (list_proj1 lvt)) VarSet.empty def) with
                    | Mgu s2 -> s2
                    | _ -> []
                ) in
                let s5 = comp_subs (apply_subs_context (match_comp_args s fcv lvt) s' VarSet.empty) in
                let sf = s5 in
                  
		let ctxt' = (rev (var2cste_listvarterm lvt ((definition2nameset def) +++ (vmdomain overload))) @ ctxt) in
                let ctxt'' = (rewrite_context_term_term ctxt' dt (App (Cons (n,Ind(iname, indargs, itype, ilc)), list_name2list_var (list_proj1 lvt)))  (*(listvarterm2varset (fcv @ ctxt))*) VarSet.empty def) in
		let ctxt''' = (apply_subs_context ctxt'' sf VarSet.empty) in
                  
                let ty' = (rewrite_term_term_term ty dt (App (Cons (n,Ind(iname, indargs, itype, ilc)), list_name2list_var (list_proj1 lvt)))  (*(listvarterm2varset (fcv @ ctxt))*) VarSet.empty  def) in
                let ty'' = (apply_subs_term ty' sf VarSet.empty) in
                  
                  
                let hdc' = (rewrite_term_term_term hdc3 dt (App (Cons (n,Ind(iname, indargs, itype, ilc)), list_name2list_var (list_proj1 lvt))) (*(listvarterm2varset (fcv @ ctxt))*) VarSet.empty  def) in
                let hdc'' = (apply_subs_term hdc' sf VarSet.empty) in
                let (lvt', _) = (decomp_foralls hdc'') in 
                let sgn = (fresh_name_list_name bv "subgoal0") in 
                  
                  
                let (l1, l2, nbg) = (destruct_build (n + 1) iname indargs itype ilc tlc args (sgn ++ bv) ty ctxt dt def overload implicite) in
                  ((fold_ctxt ctxt''' VarSet.empty def, sgn, fold ty'' VarSet.empty def)::l1, (fold (largs_lambdas (Var sgn) lvt') VarSet.empty def)::l2, nbg + 1)
                    
            | DnkMgu ->
                let hdc3 = (alpha_term_vars hdc2 (listvarterm2varset (fcv @ ctxt))) in
                let (lvt, _) = (decomp_foralls hdc3) in 
                let s' = comp_subs (
                  
                  match (unification_listterm (list_name2list_var (list_proj1 fcv)) (list_name2list_var (list_proj1 lvt)) VarSet.empty def) with
                    | Mgu s2 -> s2
                    | _ -> []
                ) in
                let sf = s' in
                  
                let ctxt' = (rev(var2cste_listvarterm lvt ((definition2nameset def) +++ (vmdomain overload))) @ ctxt) in
                let ctxt'' = (rewrite_context_term_term ctxt' dt (App (Cons (n,Ind(iname, indargs, itype, ilc)), list_name2list_var (list_proj1 lvt)))  (*(listvarterm2varset (fcv @ ctxt))*) VarSet.empty  def) in
                let ctxt''' = (apply_subs_context ctxt'' sf VarSet.empty) in
                  
                let ty' = (rewrite_term_term_term ty dt (App (Cons (n,Ind(iname, indargs, itype, ilc)), list_name2list_var (list_proj1 lvt)))  (*(listvarterm2varset (fcv @ ctxt))*) VarSet.empty  def) in
                let ty'' = (apply_subs_term ty' sf VarSet.empty) in
                  
                  
                let hdc' = (rewrite_term_term_term hdc3 dt (App (Cons (n,Ind(iname, indargs, itype, ilc)), list_name2list_var (list_proj1 lvt)))  (*(listvarterm2varset (fcv @ ctxt))*) VarSet.empty  def) in
                let hdc'' = (apply_subs_term hdc' sf VarSet.empty) in
                let (lvt', _) = (decomp_foralls hdc'') in 
                let sgn = (fresh_name_list_name bv "subgoal0") in 
                  
                  
                let (l1, l2, nbg) = (destruct_build (n + 1) iname indargs itype ilc tlc args (sgn ++ bv) ty ctxt dt def overload implicite) in
                  ((fold_ctxt ctxt''' VarSet.empty def, sgn, fold ty'' VarSet.empty def)::l1, (fold (largs_lambdas (Var sgn) lvt') VarSet.empty def)::l2, nbg + 1)
      );;


let destruct_tactic dt lg def coercion oracles overload implicite =

  match lg with
    | ((hd1,hd2,hd3)::tl,(ln,te,ty)) ->  (
        match check_term_wctxt "" hd1 dt None def coercion (varmap_vallist oracles) overload implicite with
          | None -> None
          | Some (te2, ty2) ->  
              let (t1'', args) = (decomp_app (unfold_simpl ty2 def)) in
                match (unfold_beta_red t1'' def) with
                  | Ind (x,t11, t12, t13) -> (
		      let (lsg, lmd, nbg) = (destruct_build 
                                               0
                                               x 
                                               t11 
                                               t12 
                                               t13
                                               t13
                                               args 
                                               (listvarterm2varset hd1 +++ term_var te)
                                               hd3
                                               hd1
                                               (unfold_beta_red te2 def)
                                               def
                                               overload
                                               implicite
					    ) in (
                          Some (
                            lsg @ tl,
                            (ln, var2cste (rewrite_term_var_term te hd2 (Match (te2,lmd,Some hd3,Some (Ind (x,t11, t12, t13))))) ((definition2nameset def) +++ (vmdomain overload)), ty),
                            nbg
                          )
			)
		    )
                  | _ -> None
      )
    | _ -> None
;;

let rec decalgoalsnum l n d =
  match l with
    | [] -> []
    | hd :: tl -> (
        if (hd > n) then
          (hd + d)
        else
          hd
      ) :: (decalgoalsnum tl n d)
;;

(* *)

let rec applytactics t n lgh lgg def coercion oracles overload implicite =
  if (n > 0) then (
    match t with
      | Equiv t -> 
          applyntactics (equiv_tactic t) n lgh lgg def coercion oracles overload implicite 
      | Exact t ->
          applyntactics (exact_tactic t) n lgh lgg def coercion oracles overload implicite
      | Intro -> (
          match lgh with
            | ((hd1,hd2,Forall (v,t,hd3))::tl)->  
                applyntactics (intro_tactic v) n lgh lgg def coercion oracles overload implicite
            | ((hd1,hd2,hd3)::tl) ->  (
                
                let hd3' = unfold_simpl hd3 def in
                  match hd3' with
                    | Forall (v, t1, t2) ->
                        applyntactics (intro_tactic v) n lgh lgg def coercion oracles overload implicite
                    | _ -> None
              )
            | _ -> None
        )
      | IntroAs t ->
          applyntactics (intro_tactic t) n lgh lgg def coercion oracles overload implicite
      | Apply t ->
          applyntactics (apply_tactic t) n lgh lgg def coercion oracles overload implicite
      | Generalize (t, s) ->
          applyntactics (generalize_tactic t s) n lgh lgg def coercion oracles overload implicite
      | Simpl ->
          applyntactics simpl_tactic n lgh lgg def coercion oracles overload implicite
      | SimplIn s ->
          applyntactics (simpl_in_tactic s) n lgh lgg def coercion oracles overload implicite
      | Factorize t ->
          applyntactics (factorize_tactic t) n lgh lgg def coercion oracles overload implicite
      | Destruct t ->
          applyntactics (destruct_tactic t) n lgh lgg def coercion oracles overload implicite
      | Oracle t ->
          applyntactics (oracle_tactic t) n lgh lgg def coercion oracles overload implicite
      | Fail ->
          None
      | Idtac -> 
          Some (lgh, lgg, 1)
      | TacticSeq (t1, t2) ->(
          match (applytactics t1 n lgh lgg def coercion oracles overload implicite) with
            | None -> None
            | Some (lgh2, lgg2, n2) ->
                (applytactics t2 n2 lgh2 lgg2 def coercion oracles overload implicite)
        )
      | Dotactic (n2, t) ->
          applyntactics (applydotactics t n2) n lgh lgg def coercion oracles overload implicite
      | Repeat t ->
          applyntactics (applyrepeattactics t) n lgh lgg def coercion oracles overload implicite
      | Trytactic t ->
          applyntactics (applytrytactics t) n lgh lgg def coercion oracles overload implicite
      | Partactic l ->
          applypartactics l n lgh lgg def coercion oracles overload implicite
      | Ortactic l ->
          applyntactics (applyortactics l) n lgh lgg def coercion oracles overload implicite
  ) else None

and applyntactics t n lgh lgg def coercion oracles overload implicite =
  match n with
    | 0 -> Some (lgh, lgg, 0)
    | j ->
        match (t (lgh, lgg) def coercion oracles overload implicite) with
          | None -> None
          | Some (lgh2, lgg2, n2) ->
              match (applyntactics t (j-1) (nth_tail n2 lgh2) lgg2 def coercion oracles overload implicite) with
                | None -> None
                | Some (lgh3, lgg3, n3) ->
                    Some ((nth_head n2 lgh2) @ lgh3, lgg3, n3+n2)

and applydotactics t n lg def coercion oracles overload implicite =
  let (lgh, lgg) = lg in 
    if (n <= 0) then
      Some (lgh, lgg, 0)
    else (
      match (applytactics t 1 lgh lgg def coercion oracles overload implicite) with
        | None -> None
        | Some (lgh2, lgg2, n2) ->
            applydotactics t (n-1) (lgh2, lgg2) def coercion oracles overload implicite
    )        

and applyrepeattactics t lg def coercion oracles overload implicite =
  let (lgh, lgg) = lg in 
    match (applytactics t 1 lgh lgg def coercion oracles overload implicite) with
      | None -> Some (lgh, lgg, 1)
      | Some (lgh2, lgg2, n2) ->
          match (applytactics (Repeat t) 1 lgh2 lgg2 def coercion oracles overload implicite) with
            | None -> Some (lgh2, lgg2, n2)
            | Some (lgh3, lgg3 , n3) ->
                Some (lgh3, lgg3 , n3 + n2 - 1)

and applytrytactics t lg def coercion oracles overload implicite =
  let (lgh, lgg) = lg in 
    match (applytactics t 1 lgh lgg def coercion oracles overload implicite) with
      | None -> Some (lgh, lgg, 1)
      | Some (lgh2, lgg2, n2) ->
          Some (lgh2, lgg2, n2)
            
and applypartactics l n lgh lgg def coercion oracles overload implicite =
  match l with
    | [] ->
        Some (lgh, lgg, 0)
    | hd :: tl ->
        if (n > 0) then (

          match (applytactics hd 1 lgh lgg def coercion oracles overload implicite) with
            | None -> None
            | Some (lgh2, lgg2, n2) ->
                match (applytactics (Partactic tl) 1 (nth_tail n2 lgh2) lgg2 def coercion oracles overload implicite) with
                  | None -> None
                  | Some (lgh3, lgg3, n3) ->
                      Some ((nth_head n2 lgh2) @ lgh3, lgg3, n3 + n2)

        ) else None

and applyortactics l lg def coercion oracles overload implicite =
  let (lgh, lgg) = lg in 
    match l with
      | [] ->
          None
      | hd :: tl ->
          match (applytactics hd 1 lgh lgg def coercion oracles overload implicite) with
            | None ->
                applyortactics tl (lgh, lgg) def coercion oracles overload implicite
            | Some (lgh2, lgg2, n2) ->
                Some (lgh2, lgg2, n2)

;;
