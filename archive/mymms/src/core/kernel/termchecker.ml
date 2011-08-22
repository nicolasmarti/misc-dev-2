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
open Unification;;
open Listext;;
open Unfold;;
open Fold;;
open Unfoldbetared;;
open Simpl;;
open Definition;;
open Arith;;
open Terminaison;;
open Output;;

let rec subs_filter s bv =
  match s with
    | [] -> []
    | (hd1, hd2) :: tl ->
        let tl' = subs_filter tl bv in
          if (
            (VarSet.subset (VarSet.singleton hd1) bv) &&
              (VarSet.subset (term_fv hd2 VarSet.empty) bv)
          ) then
            (hd1, hd2) :: tl'
          else
            tl'
;;

let rec subs_filter2 s bv =
  match s with
    | [] -> []
    | (hd1, hd2) :: tl ->
        if (
          (VarSet.subset (VarSet.singleton hd1) bv)) then
          (hd1, hd2) :: subs_filter2 tl (bv +++ (term_fv hd2 bv))
        else
          subs_filter2 tl bv
;;


let rec cutforallprefix_listterm n l =
  match l with
    | [] -> []
    | hd :: tl ->
        let (hdqv, hdc) = decomp_foralls hd in
        let hdqv = nth_tail n hdqv in
          (largs_foralls hdc hdqv) :: (cutforallprefix_listterm n tl)
;;

(* The set of free variables 
   use to assure the freshness

   --> initialise to empty before typechecking a term

*)

type global_fv = {
  mutable gfv: VarSet.t; 
  mutable domain: string;
};;

let tcgfv = {
  gfv = VarSet.empty; 
  domain = "";
};;

let rec termcheck 
    (* context *)
    (ctxt: context) 
    (* term to typecheck*)
    (te: term) 
    (* the expected type *)
    (ty: term option) 
    (* the set of bounded variables *)
    (bv: VarSet.t)
    (* The defined constantes *)
    (def: definition) 
    (* the coercions 
       such that (f: A , A)
    *)
    (coercion: (term * term) list)     
    (* the oracles *)
    (oracles:  (context -> term -> definition -> (term option)) list)
    (* the overloaded constantes 
       such that 
       x -> (te, ty) :: tl

       tel que x est overloade par te de type ty
       
    *)
    (overload: ((term * int) list) VarMap.t)
    (implicite: (int VarMap.t))
    (terminaison: (bexpr * (name * (int list * name list)) list))
    =  
  (*
    printf "%s |-\n%s: %s\n\n"
    (string_of_listvarterm ctxt VarMap.empty)
    (string_of_term te VarMap.empty)
    (
    match ty with
    | None -> "???"
    | Some ty ->
    (string_of_term ty VarMap.empty)
    ); flush stdout;
  *)
  match (
    match te with


      | Type -> (
          
          match ty with
              (* If we want to guess the type it is simple *)
            | None -> (([], Type, Type, [])::[])
                
            | Some ty -> 
                (* else we try the unification with the desired type*)
                match termcheckerunification ctxt ty Type bv def coercion oracles overload implicite terminaison with
                    
                  | Mgu s ->
                      (([], te, apply_subs_term ty (comp_subs s) bv, (comp_subs s))::[])
                        
                  (* Type is always of type Type such that we don't use any coercion *)
                  | _ -> []
        )

      | Avar -> (

	  (* we need a fresh variable *)
	  let te = fresh_name_list_name (tcgfv.gfv +++ bv +++ (listvarterm2varset ctxt)) "?T" in
            tcgfv.gfv <- te ++ tcgfv.gfv;
	    
	    match ty with
	      
	      | None -> (

		  let ty = fresh_name_list_name (tcgfv.gfv +++ bv +++ (listvarterm2varset ctxt)) "?T" in
		    tcgfv.gfv <- ty ++ tcgfv.gfv;

		    ((te, Var ty) :: (ty, Type)::[], Var te, Var ty, [])::[]

		)

	      | Some ty -> (

		  let oracle_res =
		    List.fold_left (
		      
		      fun acc hd ->
			match hd ctxt ty def with
			  | None -> acc
			  | Some proof ->
			      
			      let l = termcheck ctxt proof (Some ty) bv def coercion oracles overload implicite terminaison in
				l @ acc

				
		    ) [] oracles in
		    
		    match oracle_res with
		    | [] ->
			((te, ty)::[], Var te, ty, [])::[]		  
		    | _ ->
			oracle_res
		)

	)

      | Obj o -> (

          match ty with
              (* If we want to guess the type it is simple *)
            | None -> (([], Obj o, o#get_type, [])::[])

            | Some ty -> 
                (* else we try the unification with the desired type*)
                match termcheckerunification ctxt (o#get_type) ty bv def coercion oracles overload implicite terminaison with
                    
                  | Mgu s ->
                      (([], te, apply_subs_term ty (comp_subs s) bv, (comp_subs s))::[])
                        
                  (* if we cannot unify then we try to coerce *)
                  | _ -> 
                      coerce ctxt (Obj o) (o#get_type) ty bv def coercion oracles overload implicite terminaison


        )
      

      | Cste c -> (

	  let result =
	    match finddef (String.concat "." (tcgfv.domain :: c :: [])) def with
	      | Some r -> Some r
	      | None -> finddef c def

	  in

          (* find the definition and type of the constante *)
          match result with
              
              (* If not found, let's try to find if its an overloading *) 
            | None -> (

                match find_in_varmap overload c with
                    
                  (* No overloading -> this stuff is crap *)
                  | None -> []
                
                  (* This is an overloading, we check each ones as if there was a definition *)
                  | Some l -> (

                      List.fold_left (
                        
                        fun tl' hd ->

                          let (te, i) = hd in
                            
			    
                            (termcheck ctxt (App (te, list_of_n_elt Avar i)) ty bv def coercion oracles overload implicite terminaison) @ tl'
                                    
                      ) [] l


                    )
              )

            (* else we work on the returned type *)
            | Some (c, (_, ctype, nature)) -> (

                match ty with
                    
                  (* In the case of inference, it is simple *)
                  | None ->
                      ([], Cste c, ctype, [])::[]

                  (* for the case of typechecking, we use the unification/coercion solution *) 
                  | Some ty ->

                      match termcheckerunification ctxt ctype ty bv def coercion oracles overload implicite terminaison with
                          
                        | Mgu s ->
                            ([], Cste c, apply_subs_term ctype (comp_subs s) bv, (comp_subs s))::[]
                              
                        | _ -> 
			    (*printf "cannot unify %s and %s\n\n" (string_of_term ctype implicite) (string_of_term ty implicite);*)
                            coerce ctxt (Cste c) ctype ty bv def coercion oracles overload implicite terminaison
                                  
              )
        )

      | Var v -> (

          (* We first find out if the variable is bound or free *)
          match find_list ctxt v with

            (* It is a free variable *)
            | None -> (

                match ty with
                  | None ->
                      (* For type inference, we just bond it to a type variable (and we bound the type variable to the Type type) *)
                      let fv = 
                        tcgfv.gfv +++ bv                       
                      in
                      let c = fresh_name_list_name fv "?T" in
                        tcgfv.gfv <- c ++ tcgfv.gfv;
                        ((v, Var c)::(c, Type)::[], te, (Var c), [])::[]

                  | Some ty ->
                      (* We assigned it the desired type*)
                      ((v, ty)::[], te, ty, [])::[]          

              )

            (* It is a bound variable *)
            | Some vtype ->

                match ty with

                  (* inference is trivial *)
                  | None ->
                      
                      ([], te, vtype, [])::[]

                  (* for typechecking: unification/coercion *)
                  | Some ty -> (

                      match termcheckerunification ctxt vtype ty bv def coercion oracles overload implicite terminaison with

                        | Mgu s ->
                            ([], te, apply_subs_term ty (comp_subs s) bv, (comp_subs s))::[]

                        | _ -> 			    

                            coerce ctxt te vtype ty bv def coercion oracles overload implicite terminaison

                    )                               

        )

      | Let (x, t1, t2) -> (

	  (* first we infer the type of t1 *)
          let l =  termcheck ctxt t1 None bv def coercion oracles overload implicite terminaison in

            List.fold_left (
              
              fun tl' hd -> 
                let (ctxt1, te1, ty1, s1) = hd in
		  
                let t2 = apply_subs_term t2 s1 (x ++ bv) in
                let ctxt = apply_subs_context ctxt s1 bv in
		let ty = (
		  match ty with
		    | None -> None
		    | Some ty -> Some (apply_subs_term ty s1 bv)
		) in

		let l = termcheck ((x, ty1) :: ctxt1 @ ctxt) t2 ty (x ++ bv) def coercion oracles overload implicite terminaison in
		  
		  List.fold_left (
		    
		    fun tl' hd -> 
		      
		      let (ctxt2, te2, ty2, s2) = hd in

                      let te1 = apply_subs_term te1 s2 bv in
                      let ctxt1 = apply_subs_context ctxt1 s2 bv in
			
			(ctxt2 @ ctxt1, Let (x, te1, te2), ty2, comp_subs(s1 @ s2)) :: tl'

		  ) tl' l

	    ) [] l
	)
	  

      | Lambda (x, t1, t2) -> (

          (* first we verify that t1 is of type Type *)
          let l =  termcheck ctxt t1 (Some Type) bv def coercion oracles overload implicite terminaison in
            
            (* The first fold over t1 *)

            List.fold_left (
              
              fun tl' hd -> 
                let (ctxt1, te1, ty1, s1) = hd in

                (* We apply the inference *)
                let t2 = apply_subs_term t2 s1 (x ++ bv) in
                let ctxt =apply_subs_context ctxt s1 bv in
                          

                  (* let's see if we are infering or typechecking *)
                  match ty with

                    (* We are infering *)
                    | None -> (

                        (* we infer t2 knowing that x is bound *)
                        let l = termcheck ((x, te1) :: ctxt1 @ ctxt) t2 None (x ++ bv) def coercion oracles overload implicite terminaison in

                          List.fold_left (

                            fun tl' hd ->
                              let (ctxt2, te2, ty2, s2) = hd in
                                
                              (* We apply the inference *)
                              let ctxt1 = apply_subs_context ctxt1 s2 bv in
                              let te1 = apply_subs_term te1 s2 bv in

                                (ctxt2 @ ctxt1, Lambda (x, te1, te2), Forall (x, te1, ty2), comp_subs(s1 @ s2))::tl'



                          ) tl' l


                      )

                    (* We are typechecking *)
                    | Some ty -> (

                        (* we apply the inference *)
                        let ty = apply_subs_term ty s1 bv in

                          (* Let's verify that the typecheck is about a Forall *)
			  (*match unfold_beta_red ty def with*)
			let ty' = (match ty with
				     | Forall (_, _, _) -> ty
				     | _ -> simpl ty def 
				  ) in
			  
                          match ty' with
                          (* Yes, we can proceed *)
                          | Forall (y, t3, t4) -> (

                              (* We rewrite t4 such that the Lambda and the Forall quantify the same variable *)
                              let t4 = rewrite_term_var_term t4 y (Var x) in
                                                      
                              (* We apply the inference to t3 and t4 *)
                              let t3 = apply_subs_term t3 s1 bv in
                              let t4 = apply_subs_term t4 s1 bv in
                                
                                (* We typecheck t3 for Type *)
                                
                              let l = termcheck (ctxt1 @ ctxt) t3 (Some Type) bv def coercion oracles overload implicite terminaison in

                                List.fold_left (

                                  fun tl' hd ->
                                    
                                    let (ctxt3, te3, ty3, s3) = hd in

                                    (* We apply the inference *)
                                    let ctxt = apply_subs_context ctxt s3 bv in
                                    let ctxt1 = apply_subs_context ctxt1 s3 bv in
                                    let te1 = apply_subs_term te1 s3 bv in
                                    let t2 = apply_subs_term t2 s3 (x ++ bv) in
                                    let t4 = apply_subs_term t4 s3 (x ++ bv) in

                                    (* We typecheck t4 again Type (x being a bounded variable) *)
                                    let l = termcheck ((x, te3) :: ctxt3 @ ctxt1 @ ctxt) t4 (Some Type) (x ++ bv) def coercion oracles overload implicite terminaison in
                                      
                                      List.fold_left (
                                        
                                        fun tl' hd ->
                                          
                                          let (ctxt4, te4, ty4, s4) = hd in
                                            
                                          (* We apply the inference *)
                                          let ctxt = apply_subs_context ctxt s4 bv in
                                          let ctxt1 = apply_subs_context ctxt1 s4 bv in
                                          let ctxt3 = apply_subs_context ctxt3 s4 bv in
                                          let te1 = apply_subs_term te1 s4 bv in
                                          let te3 = apply_subs_term te3 s4 bv in
                                          let t2 = apply_subs_term t2 s4 (x ++ bv) in
                                            
                                          (* and finally we typecheck t2 again te4 (x being bounded) *)
                                            
                                          let l = termcheck ((x, te1) :: ctxt4 @ ctxt3 @ ctxt1 @ ctxt) t2 (Some te4)  (x ++ bv) def coercion oracles overload implicite terminaison in
                                            
                                            
                                            List.fold_left (
                                              
                                              fun tl' hd ->
                                                
                                                let (ctxt2, te2, ty2, s2) = hd in
                                                  
                                                (* We apply the inference *)
                                                let ctxt = apply_subs_context ctxt s2 bv in
                                                let ctxt1 = apply_subs_context ctxt1 s2 bv in
                                                let ctxt3 = apply_subs_context ctxt3 s2 bv in
                                                let ctxt4 = apply_subs_context ctxt4 s2 bv in
                                                let te1 = apply_subs_term te1 s2 bv in
                                                let te3 = apply_subs_term te3 s2 bv in
                                                let te4 = apply_subs_term te4 s2 (x ++ bv) in

                                                  (* We unify te1 and te3 and apply the unifier to all *) 
                                                  match termcheckerunification (ctxt3 @ ctxt1 @ ctxt) te1 te3 bv def coercion oracles overload implicite terminaison with
                                                    | Mgu s13 -> (
                                                        
                                                        let ctxt1 = apply_subs_context ctxt1 s13 bv in
							let ctxt2 = apply_subs_context ctxt2 s13 (x ++ bv) in
                                                        let ctxt3 = apply_subs_context ctxt3 s13 bv in
							let ctxt4 = apply_subs_context ctxt4 s13 bv in
                                                        let te1 = apply_subs_term te1 s13 bv in
                                                        let te3 = apply_subs_term te3 s13 bv in
                                                        let te2 = apply_subs_term te2 s13 (x ++ bv) in
                                                        let te4 = apply_subs_term te4 s13 (x ++ bv) in

                          

                                                          (* and we return the result *)
                                                          
                                                          (
                                                            ctxt2 @ ctxt4 @ ctxt3 @ ctxt1,
                                                            Lambda (x, te1, te2),
                                                            Forall (x, te3, te4),
                                                            comp_subs(s1 @ s3 @ s4 @ s2 @ s13)
                                                          ) :: tl'

                                                      )
                                                        
                                                    (* If we cannot unify there is a problem *)
                                                    | _ -> 
                                                        tl'

                                                        
                                            ) tl' l
                                              
                                      ) tl' l
                                        
                                ) tl' l

                            )

                          (* Maybe we can unify with the inference (not only for variable ???) *)
                          | ty -> (

                              let l = termcheck (ctxt1 @ ctxt) (Lambda (x, te1, t2)) None bv def coercion oracles overload implicite terminaison in

                                List.fold_left (

                                  fun tl' hd ->

                                    let (ctxt', te', ty', s') = hd in

                                    let ctxt1 = apply_subs_context ctxt1 s' bv in
                                    let ty = apply_subs_term ty s' bv in
                                      
                                      match termcheckerunification (ctxt' @ ctxt1 @ ctxt) ty' ty bv def coercion oracles overload implicite terminaison with
                                        | Mgu s -> (

                                            let ctxt1 = apply_subs_context ctxt1 s bv in
                                            let ctxt' = apply_subs_context ctxt' s bv in
                                            let te' = apply_subs_term te' s bv in
                                            let ty = apply_subs_term ty s bv in
                                            

                                              (
                                                ctxt' @ ctxt1,
                                                te',
                                                ty,
                                                comp_subs(s1 @ s' @ s)
                                              ) :: tl'
                                              
                                            

                                          )

                                        | _ -> tl'
                                      
                                  

                                ) tl' l

                            )
                              

                      )


            ) [] l


        )

      | Forall (x, t1, t2) -> (

          (* First let's verify that t1 has type Type *)

          let l = termcheck ctxt t1 (Some Type) bv def coercion oracles overload implicite terminaison in

            List.fold_left (

              fun tl' hd ->

                let (ctxt1, te1, ty1, s1) = hd in
                  
                let t2 = apply_subs_term t2 s1 (x ++ bv) in
                let ctxt = apply_subs_context ctxt s1 bv in                  
                  

                let l = termcheck ((x, te1) :: ctxt1 @ ctxt) t2 (Some Type) (x ++ bv) def coercion oracles overload implicite terminaison in
                  List.fold_left (

                    fun tl' hd ->

                      let (ctxt2, te2, ty2, s2) = hd in
                        
                      let ctxt = apply_subs_context ctxt s2 bv in                  
                      let ctxt1 = apply_subs_context ctxt1 s2 bv in                  
                      let te1 = apply_subs_term te1 s2 bv in

                        match ty with
                          | None ->
                              
                              (ctxt2 @ ctxt1, Forall (x, te1, te2), Type, s1 @ s2)::tl'
                                
                          | Some ty ->
                              
                              let ty = apply_subs_term ty (s1 @ s2) bv in
                                
                                match termcheckerunification (ctxt2 @ ctxt1 @ ctxt) ty Type bv def coercion oracles overload implicite terminaison with
                                  | Mgu s -> (
                                      
                                      let ctxt2 = apply_subs_context ctxt2 s bv in                  
                                      let ctxt1 = apply_subs_context ctxt1 s bv in                  
                                      let te1 = apply_subs_term te1 s bv in
                                      let te2 = apply_subs_term te2 s (x ++ bv) in
                                        
                                        (ctxt2 @ ctxt1, Forall (x, te1, te2), Type, comp_subs(s1 @ s2 @ s))::tl'
                                          
                                    )
                                      
                                  | _ -> tl'
                                      
                   
                  ) tl' l


            ) [] l

        )

      | Phi (x, largs, t1, ldec, body) -> (
          
          let l = termchecklargs ctxt largs bv def coercion oracles overload implicite terminaison in
            
            List.fold_left (

              fun tl' hd -> 

                let (ctxta, largs, sa) = hd in
                  
                let ctxt = apply_subs_context ctxt sa bv in
                let t1 = apply_subs_term t1 sa ((listvarterm2varset largs) +++ bv) in
                let body = apply_subs_term body sa (x ++ ((listvarterm2varset largs) +++ bv)) in
                  
                let l = termcheck ((rev largs) @ ctxta @ ctxt) t1 (Some Type) ((listvarterm2varset largs) +++ bv) def coercion oracles overload implicite terminaison in

                  List.fold_left (

                    fun tl' hd ->

                      let (ctxt1, t1, _, s1) = hd in
                      let ctxt = apply_subs_context ctxt s1 bv in
                      let ctxta = apply_subs_context ctxta s1 bv in
                      let largs = apply_subs_listvarterm largs s1 bv in
                      let body = apply_subs_term body s1 (x ++ ((listvarterm2varset largs) +++ bv)) in

		      let new_terminaison =
			
			(* TODO: this is really bad, but I do not see another way ... *)

			match ldec with
			  | None -> terminaison
			  | Some ldec ->
			      try (
				let (formula, listdec) = terminaison in
				let listname = 
				  
				  List.fold_left (
				    
				    fun tl hd ->
				      
				      tl @ (List.nth (list_proj1 largs) hd)::[]
					
				  ) [] ldec
				    
				in
				  
				  (formula, (x, (ldec, listname))::listdec)
			      ) with
				| _ -> (BFalse, [])
		      in
			
                      let l = termcheck ((x, largs_foralls t1 largs) :: ctxt1 @ (rev largs) @ ctxta @ ctxt) body (Some t1) (x ++ (listvarterm2varset largs) +++ bv) def coercion oracles overload implicite new_terminaison in
		      
                        List.fold_left (

                          fun tl' hd ->

                            let (ctxt2, body, tybody, sbody) = hd in
                            let ctxt = apply_subs_context ctxt sbody bv in
                            let ctxt1 = apply_subs_context ctxt1 sbody bv in
                            let ctxta = apply_subs_context ctxta sbody bv in
                            let largs = apply_subs_listvarterm largs sbody bv in
                            let t1 = apply_subs_term t1 sbody ((listvarterm2varset largs) +++ bv) in
                                  match ty with
                                    | None ->	(
					(*
					printf "sbody = %s\n\n" (string_of_listvarterm (sbody) VarMap.empty);
					printf "tybody = %s\n\n" (string_of_term tybody VarMap.empty);
					printf "t1 = %s\n\n" (string_of_term t1 VarMap.empty);
                                        *)
					(ctxt2 @ ctxt1 @ ctxta, 
                                        Phi (x, largs, t1, ldec, body),
                                        (largs_foralls t1 largs),
                                        comp_subs (sa @ s1 @ sbody))::tl'
				      )
                                        
                                    | Some ty ->
                                        let ty = apply_subs_term ty (comp_subs (sa @ s1 @ sbody)) bv in
                                          match 
                                            termcheckerunification 
                                              (ctxt2 @ (x, largs_foralls t1 largs) :: ctxt1 @ (rev largs) @ ctxta @ ctxt) 
                                              (largs_foralls t1 largs)
                                              ty
                                              bv 
                                              def 
                                              coercion
                                              oracles 
                                              overload
                                              implicite
					      terminaison
                                          with
                                            | Mgu se -> (
                                                
                                                let ctxta = apply_subs_context ctxta se bv in
                                                let ctxt1 = apply_subs_context ctxt1 se bv in
                                                let ctxt2 = apply_subs_context ctxt2 se bv in
                                                let largs = apply_subs_listvarterm largs se bv in
                                                let t1 = apply_subs_term t1 se ((listvarterm2varset largs) +++ bv) in
                                                let body = apply_subs_term body se (x ++ ((listvarterm2varset largs) +++ bv)) in

                                                  (
                                                    ctxt2 @ ctxt1 @ ctxta, 
                                                    Phi (x, largs, t1, ldec, body),
                                                    (largs_foralls t1 largs),
                                                    comp_subs (sa @ s1 @ sbody @ se)
                                                  )::tl'
                                              )
                                                
                                            | _ -> tl'

                        ) tl' l

                  ) tl' l

            ) [] l

        )

      | Ind (x, largs, t1, lcons) -> (

          let l = termchecklargs ctxt largs bv def coercion oracles overload implicite terminaison in

            List.fold_left (

              fun tl' hd ->

                let (ctxt1, largs, s) = hd in
                  
                let ctxt = apply_subs_context ctxt s bv in
                let t1 = apply_subs_term t1 s ((listvarterm2varset largs) +++ bv) in
                let lcons = apply_subs_listterm lcons s (x ++ ((listvarterm2varset largs) +++ bv)) in

                let l = termcheck ((rev largs) @ ctxt1 @ ctxt) t1 (Some Type) ((listvarterm2varset largs) +++ bv) def coercion oracles overload implicite terminaison in
                  
                  List.fold_left (

                    fun tl' hd ->
                      
                      let (ctxtt1, t1, _, st1) = hd in
                        
                      let ctxt = apply_subs_context ctxt st1 bv in
                      let ctxt1 = apply_subs_context ctxt1 st1 bv in
                      let largs = apply_subs_listvarterm largs st1 bv in
                      let lcons = apply_subs_listterm lcons st1 (x ++ (listvarterm2varset largs) +++ bv) in
                      let lcons = largs_foralls_listterm lcons largs in

                      let l = termchecklcons
                        ((x, largs_foralls t1 largs) :: ctxtt1 @ (rev largs) @ ctxt1 @ ctxt)
                        lcons
                        (list_of_n_elt (Some Type) (List.length lcons))                        
                        (x ++ (listvarterm2varset largs) +++ bv)
                        def
                        coercion oracles overload implicite terminaison in

                        List.fold_left (

                          fun tl' hd ->

                            let (ctxtlcons, lcons, _, slcons) = hd in
                              
                            let lcons = cutforallprefix_listterm (List.length largs) lcons in
                            let ctxt = apply_subs_context ctxt slcons bv in
                            let ctxt1 = apply_subs_context ctxt1 slcons bv in
                            let ctxtt1 = apply_subs_context ctxtt1 slcons bv in                                
                            let largs = apply_subs_listvarterm largs slcons bv in
                              
                            (*let lcons = apply_subs_listterm lcons slcons fv in*)
                            let t1 = apply_subs_term t1 slcons bv in
                                match ty with
                                  | None -> (

                                      (
                                        ctxtlcons @ ctxtt1 @ ctxt1,
                                        fold (Ind (x, largs, t1, lcons)) bv def,
                                        (largs_foralls t1 largs),
                                        comp_subs (s @ st1 @ slcons)
                                      )::tl'

                                    )
                                  | Some ty ->
                                      let ty = apply_subs_term ty (comp_subs (s @ st1 @ slcons)) bv in
                                        
                                      match termcheckerunification 
                                        ((x, largs_foralls t1 largs) :: ctxtlcons @ ctxtt1 @ (rev largs) @ ctxt1 @ ctxt)
                                        (largs_foralls t1 largs)
                                        ty                                          
                                        bv 
                                        def coercion oracles overload implicite terminaison 
                                        with
                                          | Mgu s' ->
                                              let ctxt1 = apply_subs_context ctxt1 s' bv in
                                              let ctxtt1 = apply_subs_context ctxtt1 s' bv in 
                                              let ctxtlcons = apply_subs_context ctxtlcons s' bv in 
                                              let lcons = apply_subs_listterm lcons s' bv in
                                              let t1 = apply_subs_term t1 s' bv in
                                              let largs = apply_subs_listvarterm largs s' bv in
                                                (
                                                  ctxtlcons @ ctxtt1 @ ctxt1,
                                                  fold (Ind (x, largs, t1, lcons)) bv def,
                                                  (largs_foralls t1 largs),
                                                  comp_subs (s @ st1 @ slcons @ s')
                                                ) :: tl'
                                          | _ -> tl'
                                              

                        ) tl' l

                  ) tl' l

            ) [] l

        )

      | Cons (n, t1) -> (

          let l = termcheck ctxt t1 None bv def coercion oracles overload implicite terminaison in

            List.fold_left (

              fun tl' hd ->

                let (ctxt1, t1, ty1, s1) = hd in 

		  (*match (unfold_beta_red t1 def) with*)
		  match (unfold_simpl t1 def) with
                    | Ind (x, largs, ty', lcons) -> (
                        
			let tye = largs_foralls (rewrite_term_var_term (List.nth lcons n) x t1) largs in
                        (*let tye = largs_foralls (rewrite_term_var_term (List.nth lcons n) x (Ind (x, largs, ty', lcons))) largs in*)
                        let te = Cons (n, t1) in
                        
                          match ty with
                            | None -> 
                                (
                                  ctxt1,
                                  te,
                                  tye,
                                  comp_subs (s1)
                                ):: tl'

                            | Some ty -> (
                                
                                let ty = apply_subs_term ty s1 bv in
                                let ctxt = apply_subs_context ctxt s1 bv in
                                  
                                match termcheckerunification (ctxt1 @ ctxt) tye ty bv def coercion oracles overload implicite terminaison with                                  
                                  | Mgu s ->
                                      let ctxt1 = apply_subs_context ctxt1 s bv in
                                      let tye = apply_subs_term tye s bv in
                                      let te = apply_subs_term te s bv in
                                        (
                                          ctxt1,
                                          te,
                                          tye,
                                          comp_subs (s1 @ s)
                                        )::tl'
                                  | _ -> tl'
                              )
                      )
                    | _ -> tl'
                        
            ) [] l
        )

      | Match (x, ldes, dty, ind) -> (

          match dty with
            | None -> (
              
                let l = termcheck ctxt x None bv def coercion oracles overload implicite terminaison in
                  
                  List.fold_left (
                    fun tl' hd ->
                      let (ctxtx, x, tyx, sx) = hd in
                      let ldes = apply_subs_listterm ldes sx bv in
                      let ctxt = apply_subs_context ctxt sx bv in
                      (*let (fct, args) = decomp_app (unfold_beta_red tyx def) in *)
		      let (fct, args) = decomp_app (unfold_simpl tyx def) in

                        match (unfold_simpl fct def) with
                          | (Ind (ind_name, ind_args, ind_ty, ind_lcons)) -> (
                              
			      let ty' = 
                                match ty with
                                  | None -> Type
                                  | Some ty -> apply_subs_term ty sx bv
                              in                            

                                match destruct_cases (ctxtx @ ctxt) x ty' args 0 ldes ind_lcons ind_name ind_args ind_ty ind_lcons  bv def coercion oracles overload implicite terminaison with
                                  | None -> print_error "destruct failed !\n"; tl'
                                  | Some (l1, l2, l3, l4, l5, l6, sd) ->
                              
                                      let ctxt = apply_subs_context ctxt sd bv in
				      let ctxtx = apply_subs_context ctxtx sd bv in

				      let l4' = (
					
					List.map (
					  
					  fun hd ->
					    (list2varset (list_proj1 hd))
					      
					) l4
					  
				      ) in

                                      match ty with
                                        | None -> (
				    
                                            let l = termcheckldes (ctxtx @ ctxt) l1 l2 (list_of_n_elt None (List.length l1)) l4' bv def coercion oracles overload implicite l6 in
		                              List.fold_left (
                                                fun tl' hd ->
                                                  let (lctxt, ldes', lty, s) = hd in

                                                  let s' = comp_subs (sd @ s) in
                                                    
                                                  (* How to infer the most general type from all the lty ??? *)
                                                  (* Now, the solution is REALLY primitive ... *)

                                                  (*let ldes = apply_subs_listterm ldes s bv in*)

						  let ldes =

						    List.map (
						      
						      fun hd ->

							let (qv, ccl) = hd in
							  
							let qv = rev (apply_subs_context (rev qv) s' bv) in
							  
							  (largs_lambdas ccl qv)
						      

						    ) (List.combine l4 ldes') in

						  let ldes =
						    list_insert ldes l5 Type
						  in

                                                  let ctxtx = apply_subs_context ctxtx s' bv in
                                                  let ctxt = apply_subs_context ctxt s' bv in
						  let x = apply_subs_term x s' bv in
													

                                                    (*match listtypeeq (lctxt @ ctxtx @ ctxt) (List.hd lty) (List.tl lty) bv def coercion oracles overload implicite with*)
						    match listtyunif (lctxt @ ctxtx @ ctxt) (List.hd lty) (List.tl lty) bv def coercion oracles overload implicite terminaison with
                                                      | None -> print_error "inference of final type failed\n"; tl'
                                                      | Some (ty, s'') ->
							  
							  let ldes = apply_subs_listterm ldes s'' bv in
							  let ctxtx = apply_subs_context ctxtx s'' bv in
							  let ctxt = apply_subs_context ctxt s'' bv in
							  let lctxt = apply_subs_context lctxt s'' bv in
							  let x = apply_subs_term x s'' bv in


							  let l = termcheck (lctxt @ ctxtx @ ctxt) ty (Some Type) bv def coercion oracles overload implicite terminaison in
							    
							    List.fold_left (
							      
							      fun tl' hd ->

								let (tyctxt, ty, _, tys) = hd in

								let ldes = apply_subs_listterm ldes tys bv in
								let ctxtx = apply_subs_context ctxtx tys bv in
								let lctxt = apply_subs_context lctxt tys bv in
								let x = apply_subs_term x tys bv in

								  (tyctxt @ lctxt @ ctxtx, Match (x, ldes, None, Some ((Ind (ind_name, ind_args, ind_ty, ind_lcons)))), ty, comp_subs (sx @ s' @ s'' @ tys))::tl'
								  
							    ) tl' l
                                              ) tl' l
                                                
                                          )

                                        | Some ty -> (

                                            let ty = apply_subs_term ty (comp_subs (sx @ sd)) bv in
                                              
                                            let l = termcheckldes (ctxtx @ ctxt) l1 l2 (list2listoption l3) l4' bv def coercion oracles overload implicite l6 in
                                                  
                                              List.fold_left (
                                                fun tl' hd ->
                                                  let (lctxt, ldes', lty, s) = hd in

                                                  let s' = comp_subs (sd @ s) in
                                                    
						  let ldes =

						    List.map (
						      
						      fun hd ->

							let (qv, ccl) = hd in
							  
							let qv = rev (apply_subs_context (rev qv) s' bv) in
							  
							  (largs_lambdas ccl qv)
						      

						    ) (List.combine l4 ldes') in

						  let ldes =
						    list_insert ldes l5 Type
						  in
						    
                                                  let ctxtx = apply_subs_context ctxtx s' bv in
						  let ctxt = apply_subs_context ctxt s' bv in
                                                  let ty = apply_subs_term ty s bv in
                                                  let x = apply_subs_term x s' bv in

						  let l = termcheck (lctxt @ ctxtx @ ctxt) ty (Some Type) bv def coercion oracles overload implicite terminaison in
                                                    
						    List.fold_left (
						      
                                                      fun tl' hd ->
							let (tyctxt, ty, _, tys) = hd in
							  
							let ctxtx = apply_subs_context ctxtx tys bv in
							let lctxt = apply_subs_context lctxt tys bv in
							let x = apply_subs_term x s' bv in
							let ldes = apply_subs_listterm ldes tys bv in							  
						      
							  (tyctxt @ lctxt @ ctxtx, Match (x, ldes, None, Some (Ind (ind_name, ind_args, ind_ty, ind_lcons))), ty, comp_subs (sx @ sd @ s @ tys))::tl'
							    
						    ) tl' l


                                              ) tl' l
                                  )
                            )
                          | x -> print_error (sprintf "Cannot identify with an inductive type ! ( == %s) \n" (string_of_term x implicite)); tl'
                  ) [] l
                    
              )

            | Some dty -> (

                let l = termcheck ctxt dty (Some Type) bv def coercion oracles overload implicite terminaison in

                List.fold_left (
                  
                  fun tl' hd ->

                    let (ctxtdty, dty, tydty, sdty) = hd in
                      
                    let ctxt = apply_subs_context ctxt sdty bv in
                    let ldes = apply_subs_listterm ldes sdty bv in
                    let x = apply_subs_term x sdty bv in
                        
                      match ty with
                        | None -> (
                            
                            let l = termcheck (ctxtdty @ ctxt) (Match (x, ldes, None, ind)) (Some dty) bv def coercion oracles overload implicite terminaison in

                              List.fold_left (
                                fun tl' hd ->
                                  let (ctxt1, te1, ty1, s1) = hd in
                                  let ctxtdty = apply_subs_context ctxtdty s1 bv in
                                  let dty = apply_subs_term dty s1 bv in
                                      
                                    match te1 with
                                      | Match (x, ldes, None, ind) ->
                                          (ctxt1 @ ctxtdty, Match (x, ldes, (Some dty), ind), dty, comp_subs (sdty @ s1))::tl'
                                      | _ -> tl'
                                            
                              ) tl' l
                            )
                              
                          | Some ty -> (
                              
                              let ty = apply_subs_term ty sdty bv in

			      let l = termcheck (ctxtdty @ ctxt) ty (Some Type) bv def coercion oracles overload implicite terminaison in
                                
				List.fold_left (
						      
				  fun tl' hd ->
                                    let (tyctxt, ty, _, tys) = hd in
                                				      
                                      let ctxtdty = apply_subs_context ctxtdty tys bv in
				      let dty = apply_subs_term dty tys bv in
				      let ldes = apply_subs_listterm ldes tys bv in
				      let x = apply_subs_term x tys bv in
                                            
                                      match termcheckerunification (tyctxt @ ctxtdty @ ctxt) dty ty bv def coercion oracles overload implicite terminaison with
					| Mgu s -> (
					    
					    let ctxtdty = apply_subs_context ctxtdty s bv in
					    let tyctxt = apply_subs_context tyctxt s bv in
					    let dty = apply_subs_term dty s bv in
					    let ldes = apply_subs_listterm ldes s bv in
					    let x = apply_subs_term x s bv in
                                              
					    let l = termcheck (tyctxt @ ctxtdty @ ctxt) (Match (x, ldes, None, ind)) (Some dty) bv def coercion oracles overload implicite terminaison in
					      
                                              List.fold_left (
						fun tl' hd ->
						  let (ctxt1, te1, ty1, s1) = hd in
						    
						  let ctxtdty = apply_subs_context ctxtdty s1 bv in
						  let tyctxt = apply_subs_context tyctxt s1 bv in
						  let dty = apply_subs_term dty s1 bv in
                                                    
						    match te1 with
                                                      | Match (x, ldes, None, ind) ->
							  (ctxt1 @ tyctxt @ ctxtdty, Match (x, ldes, (Some dty), ind), dty, comp_subs (sdty @ s @ s1 @ tys))::tl'
                                                      | _ -> tl'                                                    
                                              ) tl' l                                                      
					  )                                      
					| _ -> tl'                          

				) tl' l
			    )
                ) [] l
		  
              )

        )

      | AdvMatch (t, ldes, mty) -> (
	  
	  if (VarSet.is_empty (term_varfct t def)) then (
	    
	    (*printf "AdvMatch:\n%s\n\n" (string_of_term (AdvMatch (t, ldes, ty)) implicite);*)

	    let (list_lhs_ldes, list_rhs_ldes) = List.split ldes in
	    let ldes_size = List.length list_lhs_ldes in

	    (* inference of l.h.s *)
	    let l = termcheckldes ctxt 
	      (list_of_n_elt [] ldes_size) 
	      list_lhs_ldes
	      (list_of_n_elt None ldes_size) 
	      (list_of_n_elt VarSet.empty ldes_size)  
	      bv def coercion oracles overload implicite (list_of_n_elt (BTrue, []) ldes_size) in


	      List.fold_left (

		fun tl' hd ->

                  let (lctxt, ldes, lty, s) = hd in

		  let ctxt = apply_subs_context ctxt s bv in
		  let t = apply_subs_term t s bv in
		  let mty = 
		    match mty with
		      | None -> None
		      | Some mty -> Some (apply_subs_term mty s bv)
		  in
		  let ty = 
		    match ty with
		      | None -> None
		      | Some ty -> Some (apply_subs_term ty s bv)
		  in

		  let list_rhs_ldes = 
		    List.map (

		      fun hd ->
			
			let (t1, t2) = hd in
			  
			  apply_subs_term t2 s (bv +++ (term_var t1))

		    ) (List.combine ldes list_rhs_ldes)		    
		  in
		    
		    (*
		      printf "AdvMatch:\n%s\n\n" (string_of_listterm (list_lhs_ldes) VarMap.empty);
		      printf "AdvMatch:\n%s\n\n" (string_of_listterm lty VarMap.empty);
		    *)

		    (* unification of all types of l.h.s  *)
		  let (infered_ty, s') = (
		    match listtyunif (lctxt @ ctxt) (List.hd lty) (List.tl lty) bv def coercion oracles overload implicite terminaison with
                      | None -> (None, [])
                      | Some (infered_ty, s') -> (Some infered_ty, s')
		  ) in

                  (*
		  printf "AdvMatch:\n%s\n\n" (
		    match infered_ty with
		      | None -> "None"
		      | Some ty -> (string_of_term ty implicite)
		  );
		  *)
			  
		  let ctxt = apply_subs_context ctxt s' bv in
		  let lctxt = apply_subs_context lctxt s' bv in
		  let t = apply_subs_term t s' bv in
		  let mty = 
		    match mty with
		      | None -> None
		      | Some mty -> Some (apply_subs_term mty s' bv)
		  in
		  let ty = 
		    match ty with
		      | None -> None
		      | Some ty -> Some (apply_subs_term ty s' bv)
		  in
		  let ldes = apply_subs_listterm ldes s' bv in
		  let list_rhs_ldes = 
		    List.map (
		      
		      fun hd ->
			
			let (t1, t2) = hd in
			  
			  apply_subs_term t2 s' (bv +++ (term_var t1))
			    
		    ) (List.combine ldes list_rhs_ldes)
		  in
		    
		  (* termcheck t versus infered_ty *)
		  let l = termcheck (lctxt @ ctxt) t infered_ty bv def coercion oracles overload implicite terminaison in
		    
		    List.fold_left (
		      
		      fun tl' hd ->
			
			let (tctxt, t, tty, ts) = hd in
			  
			let ldes = apply_subs_listterm ldes ts bv in
			let list_rhs_ldes = 
			  List.map (
			    
			    fun hd ->
			      
			      let (t1, t2) = hd in
				
				apply_subs_term t2 ts (bv +++ (term_var t1))
				  
			  ) (List.combine ldes list_rhs_ldes)
			in
			let ctxt = apply_subs_context ctxt ts bv in
			let lctxt = apply_subs_context lctxt ts bv in
			let mty = 
			  match mty with
			    | None -> None
			    | Some mty -> Some (apply_subs_term mty ts bv)
			in				
			let ty = 
			  match ty with
			    | None -> None
			    | Some ty -> Some (apply_subs_term ty ts bv)
			in				
			  
			  
			(* we look for a l.h.s. that unify with t, but not on t variables *)
			let nt = 
			  List.fold_left (
			    
			    fun tl' hd ->
			      
			      match tl' with
				  
				(* We will need somme unfolding *)
				| (None, l) -> (None, l)
				    
				(* we have found a candidate destructor *)
				| (Some (Some _), _) -> tl'
				    
				(* we are still looking *)
				| (Some None, _) ->
				    
				    let (hd1, hd2) = hd in
				      
				      (*
					printf "unification:\n%s Vs %s\n\n" (string_of_term t VarMap.empty) (string_of_term hd1 VarMap.empty);
				      *)
				      
				      match termcheckerunification (tctxt @ lctxt @ ctxt) hd1 t VarSet.empty def coercion oracles overload implicite terminaison with
					| Mgu s -> (
					    
					    (*
					      printf "unification .... ";
					    *)
					    
					    let svar = list2varset (list_proj1 s) in
					    let tvar = (term_var t) in
					    let inter = VarSet.inter svar tvar in
					      
					      (* the unification is on t variables ??? *)
					      if (VarSet.is_empty inter) then
						(
							  
						  (*
						    printf "ok!!\n\n ";
						  *)
						  
						  let hd2 = apply_subs_term hd2 s bv in
							  let hd2 = (alpha_term_vars hd2 bv) in
							    (Some (Some hd2), [])
							      
						)
					      else
						(
						  
						  (*
						    printf "will need some unfolding ... \n\n ";
						  *)
						  
						  (None, VarSet.elements inter)
						    
						)
					  )
					| _ -> 
					    
					    (*
					      printf "no unification ....\n\n";
					    *)
					    
					    (Some None, [])
					      
			  ) (Some None, []) (List.combine ldes list_rhs_ldes) in
			  
			  match nt with
			    | (None, hd::tl) -> (
				
				
				(*
				  printf "AdvMatch: need to unfold \n";
				*)
				
				(* let's look at the type of the variable to know how to unfold *)
				
				let l = termcheck (tctxt @ lctxt @ ctxt) (Var hd) None bv def coercion oracles overload implicite terminaison in
				  
				  List.fold_left (
				    
				    fun tl' hd ->
				      
				      let (vctxt, v, vty, vs) = hd in
					
				      let ldes = apply_subs_listterm ldes vs bv in
				      let list_rhs_ldes = 
					List.map (
					  
					  fun hd ->
					    
					    let (t1, t2) = hd in
					      
					      apply_subs_term t2 vs (bv +++ (term_var t1))
						
					) (List.combine ldes list_rhs_ldes)
				      in
				      let ctxt = apply_subs_context ctxt vs bv in
				      let lctxt = apply_subs_context tctxt vs bv in
				      let tctxt = apply_subs_context tctxt vs bv in
				      let mty = 
					match mty with
					  | None -> None
					  | Some mty -> Some (apply_subs_term mty vs bv)
				      in				
				      let ty = 
					match ty with
					  | None -> None
					  | Some ty -> Some (apply_subs_term ty vs bv)
				      in				
				      let t = apply_subs_term t vs bv in					      

				      let (fct, args) = decomp_app (unfold_simpl vty def) in
					
					match (unfold_simpl fct def) with
					  | (Ind (ind_name, ind_args, ind_ty, ind_lcons)) -> (

					      (*
						printf "ind_lcons:= %s\n\n" (string_of_listterm ind_lcons VarMap.empty);
					      *)

					      let nldes = 
						List.map (
						  
						  fun hd ->

						    let (lh, _) = decomp_foralls hd in
						    let lh_size = (List.length lh + List.length ind_args) in
						    let fvs = fresh_names2 (tcgfv.gfv +++ bv +++ (listvarterm2varset (tctxt @ ctxt))) lh_size "?T" in
						      tcgfv.gfv <- (list2varset fvs) +++ tcgfv.gfv;
						      
						      let nlh = List.combine fvs (list_of_n_elt Avar lh_size) in
							
							largs_lambdas (AdvMatch (t, (List.combine ldes list_rhs_ldes), mty)) nlh


						) ind_lcons in

					      let nt = Match (v, nldes, mty, None) in

					      (*
						printf "nt:= %s\n\n" (string_of_term nt VarMap.empty);
					      *)

					      let l = termcheck (tctxt @ lctxt @ ctxt) nt ty bv def coercion oracles overload implicite terminaison in

						List.fold_left (

						  fun tl' hd ->

						    let (fctxt, ft, fty, fs) = hd in

						    let tctxt = apply_subs_context tctxt fs bv in
						    let lctxt = apply_subs_context lctxt fs bv in
						    let vctxt = apply_subs_context vctxt fs bv in

						      (fctxt @ vctxt @ tctxt @ lctxt, ft, fty, comp_subs (s @ s' @ ts @ vs @ fs))::tl'

						) tl' l

					    )

					  | tt -> 
					      
					      print_error (sprintf "AdvMatch: term is not of inductive type ... \n%s := %s\n\n" (string_of_term v VarMap.empty) (string_of_term vty VarMap.empty));

					      print_error (
						  String.concat " " (["otherchoices: "] @
								       (List.map (fun hd -> String.concat "" (
										    ["("; (string_of_term (Var hd) VarMap.empty); ")"; "\n\n"])) tl)
								    )
					      );

					      tl'

				  ) tl' l
				    
			      )					 

			    | (Some None, _) -> (

				(* problem *)
				let (mistype, err) = 
				  let lty = tty :: lty in
				  let lty = List.map (fun hd -> 
							let hd = app_nf hd in
							let (_, hd) = decomp_foralls hd in
							let (hd, _) = decomp_app hd in
							  hd
						     ) lty in
				  
				    match listtyunif (tctxt @ lctxt @ ctxt) (List.hd lty) (List.tl lty) bv def coercion oracles overload implicite terminaison with
				      | None -> (true, lty)
				      | Some _ -> (false, [])
				in

				  if mistype then (
				    print_error (sprintf "mistype in destructor, one with type: %s\n" (string_of_listterm err implicite));
				    tl'
				  )
				  else				
				    match te with
				      | AdvMatch (t, ldes, mty) -> (
					  
					  let v = fresh_name_list_name (tcgfv.gfv +++ bv +++ (listvarterm2varset ctxt)) "?T" in
					    tcgfv.gfv <- v ++ tcgfv.gfv;		
					    let te = Let(v, t, AdvMatch (Var v, ldes, mty)) in
					      
					    let l = termcheck (tctxt @ lctxt @ ctxt) te ty bv def coercion oracles overload implicite terminaison in
					      
					      List.fold_left (
						
						fun tl' hd ->
						  
						  let (fctxt, ft, fty, fs) = hd in
						    
						  let tctxt = apply_subs_context tctxt fs bv in
						  let lctxt = apply_subs_context lctxt fs bv in
						    
						    (fctxt @ tctxt @ lctxt, ft, fty, comp_subs (s @ s' @ ts @ fs))::tl'
						      
						      
					      ) tl' l
						
					)
				      | _ -> tl'
					  
			      )
				
			    | (Some (Some t), _) -> (

				let l = termcheck (tctxt @ ctxt) t ty bv def coercion oracles overload implicite terminaison in

				  List.fold_left (
				    
				    fun tl' hd ->

				      let (fctxt, ft, fty, fs) = hd in

				      let tctxt = apply_subs_context tctxt fs bv in
				      let lctxt = apply_subs_context lctxt fs bv in

					(fctxt @ tctxt @ lctxt, ft, fty, comp_subs (s @ s' @ ts @ fs))::tl'


				  ) tl' l

			      )

			    | _ -> print_error "couille & potage\n\n"; tl'

		    ) tl' l

	      ) [] l

	  ) else (

	    let v = fresh_name_list_name (tcgfv.gfv +++ bv +++ (listvarterm2varset ctxt)) "?T" in
	      tcgfv.gfv <- v ++ tcgfv.gfv;		
	      let te = Let(v, t, AdvMatch (Var v, ldes, mty)) in
		termcheck ctxt te ty bv def coercion oracles overload implicite terminaison

	  )

	)

      | App (t1, t2) -> (

          let l = termcheck ctxt t1 None bv def coercion oracles overload implicite terminaison in

            List.fold_left (

              fun tl' hd ->

                let (ctxt1, t1, ty1, s1) = hd in

                let ctxt = apply_subs_context ctxt s1 bv in
                let t2 = apply_subs_listterm t2 s1 bv in

                let l = termcheckapp (ctxt1 @ ctxt) t1 t2 ty1 bv def coercion oracles overload implicite terminaison in
		  
                  List.fold_left (

                    fun tl' hd ->

                      let (ctxt2, t, ty2, s2) = hd in

                      let ctxt1 = apply_subs_context ctxt1 s2 bv in
                      let ctxt = apply_subs_context ctxt s2 bv in

		      (* terminaison test *)
		      let (fctt, argt) = decomp_app t in

		      let terminate = (

			match fctt with
			  | Var x -> (
			      
			      let (formula, listdec) = terminaison in

				match find_list listdec x with

				  | None -> true

				  | Some (list_ind, list_names) -> (
				
				      try (

					let list_term =
					  
					  List.fold_left (

					    fun tl hd ->
					      
					      tl @ (List.nth argt hd)::[]

					  ) [] list_ind in

					  match (sum_term_size_arith list_term def, sum_term_size_arith (List.map (fun x -> Var x) list_names) def) with
					    | (Some sum, Some sum') -> (
						
						if (fm_dp (bimpl formula (Blt (sum, sum')))) then true
						else (print_error "terminaison pbme3 : \n"; (*(print_bexpr (bimpl formula (Blt (sum, sum')))); printf "\n\n"; *) false)
						
					      )
					    | _ -> print_error (sprintf "terminaison pbm1: (%s, %s)\n\n" (string_of_listterm list_term VarMap.empty) (string_of_listterm (List.map (fun x -> Var x) list_names) VarMap.empty)); false

				      ) with
					| _ -> print_error "terminaison pbm2\n\n"; false

				    )
			      )

			    | _ -> true

			) in


			  if (terminate) then
			    (

                              match ty with
				| None ->
                                    ((ctxt2 @ ctxt1), t, ty2, comp_subs (s1 @ s2))::tl'

				| Some ty ->
                                    let ty = apply_subs_term ty (comp_subs (s1 @ s2)) bv in

                                      match termcheckerunification (ctxt2 @ ctxt1 @ ctxt) ty2 ty bv def coercion oracles overload implicite terminaison with
					| Mgu s -> (
					    
					    let ctxt1 = apply_subs_context ctxt1 s bv in
					    let ctxt2 = apply_subs_context ctxt2 s bv in
					    let t = apply_subs_term t s bv in
					    let ty = apply_subs_term ty s bv in
                                              
                                              ((ctxt2 @ ctxt1), t, ty, comp_subs (s1 @ s2 @ s))::tl'

					  )                                      
					| s -> 

					    (*
					      printf "App problem: unification (%s) \n%s\n VS \n%s\n\n"
						(match s with
						   | NoMgu -> "NoMgu"
						   | DnkMgu -> "DnkMgu"
						   | Mgu s -> "fatal error !!!!"
						)
						(string_of_term ty2 implicite)
						(string_of_term ty implicite);
					    *)

					    let l = coerce (ctxt2 @ ctxt1 @ ctxt) t ty2 ty bv def coercion oracles overload implicite terminaison in
                                              
                                              List.fold_left (

						fun tl' hd ->

						  let (ctxt3, t3, ty3, s3) = hd in
						  let ctxt1 = apply_subs_context ctxt1 s3 bv in
						  let ctxt2 = apply_subs_context ctxt2 s3 bv in

						    ((ctxt3 @ ctxt2 @ ctxt1), t3, ty3, comp_subs (s1 @ s2 @ s3))::tl'
						      
                                              )  tl' l
			    ) else (

			      (*printf "does not terminate!!\n\n";*)

			      tl'

			    )

                  ) tl' l                  

            ) [] l

        )

  ) with
    | l -> 
        if (List.length l = 0) then (

          print_error (
	    sprintf "--------\nError\n--------\n\n{\n%s}%s|-\n%s: %s\n"
	      (
		let l = (
		  (term_cons te) +++ (
		    match ty with 
		      | None -> VarSet.empty
		      | Some ty -> term_cons ty
		  )
		) in
		  List.fold_left (
		    
		    fun acc hd ->
		      
		      match finddef hd def with
			| Some (name, (te, ty, nature)) ->
			    concat "" (acc :: hd :: ":= " ::(string_of_term te implicite) :: ": " :: (string_of_term ty implicite) :: "\n" ::[])
			| _ -> (*concat "" (hd :: " does not exists!!!!" :: [])*) ""
			    
		  ) "" (VarSet.elements l)
		    
	      )
              (string_of_listvarterm ctxt VarMap.empty)
              (string_of_term te VarMap.empty)
              (match ty with
		 | None -> "??"
		 | Some ty -> string_of_term ty VarMap.empty
              )
	  );
	  (*
	  let (formula, _) = (terminaison) in
	     (print_bexpr formula);
	  *)
	  print_error "\n-------\n\n";	  

          []
        ) else
	  let init_ctxt = ctxt in

	  (* let's try to resolve some context variables through the oracles *)
          List.fold_left (

            fun acc hd ->

	      (* here is one solution from the termchecker *)

              let (ctxt, te, ty, s) = hd in
	      let init_ctxt = apply_subs_context init_ctxt s bv in

		(*
	      let ctxt = apply_subs_context ctxt s VarSet.empty in
	      let te = apply_subs_term te s VarSet.empty in
	      let ty = apply_subs_term ty s VarSet.empty in
		*)

	      (* FIXED
		  FIXME: this is an ugly patch ... FIND where the rewrite of substitution does not not perform on the ctxt *)
		(*
	      let ctxt2 = apply_subs_context ctxt s VarSet.empty in
	      let te2 = apply_subs_term te s VarSet.empty in
	      let ty2 = apply_subs_term ty s VarSet.empty in
		
		if (term_eq te2 te def && term_eq ty2 ty def && 
		      
		      List.fold_left (

			fun acc hd ->
			  let ((_, hd1), (_, hd2)) = hd in
			  acc && (term_eq hd1 hd2 def)
			  
		      ) true (combine ctxt2 ctxt)
		   ) then
		  () else
		    (
		      printf "\n[%s] |-\n%s: %s\nVs\n[%s] |-\n%s: %s\n\n(%s)\n\n"
			(string_of_listvarterm ctxt VarMap.empty)
			(string_of_term te VarMap.empty)
			(string_of_term ty VarMap.empty)
			(string_of_listvarterm ctxt2 VarMap.empty)
			(string_of_term te2 VarMap.empty)
			(string_of_term ty2 VarMap.empty)
			(string_of_listvarterm s VarMap.empty)
		    );*)
		(**)
	      (* what are the (possible) unresolve free variable *)
	      let unresolved = subs_filter2 ctxt ((term_fv te bv) +++ (term_fv ty bv)) in

	      let nhd = 
		match unresolved with
		  | [] ->

		      (* None there, let's continue *)
		      (ctxt, te, (*simpl ty def*) ty, (comp_subs s))::[]

		  | l -> (

		      (* there is a list l of unresolved variable *)
		      List.fold_left (
			
			fun acc hd ->

			  (* we have an unresolved variable v of type v_ty *)
			  let (v, v_ty) = hd in

			    (*printf "looking for %s:%s ... in %s \n" v (string_of_term v_ty VarMap.empty) (string_of_listvarterm ((list_remove_fst v ctxt) @ init_ctxt) VarMap.empty);*)
			    
			  (* here are the possibilities *)
			  let nv =
			    			    
			    List.fold_left (
			      
			      fun acc hd ->
				match hd ((*(list_remove_fst v ctxt)*) ctxt @ init_ctxt) v_ty def with
				  | None -> acc
				  | Some proof ->

				      let l = termcheck (ctxt @ init_ctxt) proof (Some v_ty) bv def coercion oracles overload implicite terminaison in
					l @ acc
					  
					  
			    ) [] oracles in			    

			    (* we should now rewrite the possibilities in the solutions *)

			    List.fold_left (

			      fun acc hd ->

				let (ctxt, te, ty, s) = hd in
				  
				  List.map (

				    fun hd ->

				      let (ctxt', te', ty', s') = hd in
					
				      let ctxt' = apply_subs_context ctxt' s bv in
				      let te' = apply_subs_term te' s bv in
				      let ty' = apply_subs_term ty' s bv in

					(*printf "rewrite %s in %s as %s\n\n"
					  v
					  (string_of_term te' VarMap.empty)
					  (string_of_term te VarMap.empty);
					*)

					(ctxt @ ctxt', 
					 rewrite_term_var_term te' v te,
					 rewrite_term_var_term ty' v te,
					 comp_subs (s @ s')
					)					

				  ) acc

			    ) acc nv

		      ) ((ctxt, te, (*simpl ty def*) ty, (comp_subs s))::[]) l

		    ) 
	      in

	      nhd @ acc
                  
          ) [] l


and termcheckapp ctxt te args ty bv def coercion oracles overload implicite terminaison =
  match args with
    | [] -> ([], app_nf te, ty, [])::[]
    | hd :: tl -> (

	let ty = (match ty with
		     | Forall (_, _, _) -> ty
		     | _ -> simpl ty def 
		  ) in
  
          match ty with
            | Forall (x, ty1, ty2) -> (

                let l = termcheck ctxt hd (Some ty1) bv def coercion oracles overload implicite terminaison in
                  
                  List.fold_left (

                    fun tl' hd ->
                      
                      let (hdctxt, hdte, hdty, hds) = hd in
                        
                      let ctxt = apply_subs_context ctxt hds bv in
                      let te = apply_subs_term te hds bv in
                      let tl = apply_subs_listterm tl hds bv in
                      let ty2 = apply_subs_term ty2 hds (x ++ bv) in

                      let ty = (rewrite_term_var_term (alpha_term_vars ty2 (term_fv hdte VarSet.empty)) x hdte) in
                        
                      let l = termcheckapp (hdctxt @ ctxt) (App (te, hdte::[])) tl ty bv def coercion oracles overload implicite terminaison in

                        List.fold_left (

                          fun tl' hd ->
                            
                            let (tlctxt, tlte, tlty, tls) = hd in
                            let hdctxt = apply_subs_context hdctxt tls bv in
                              
                              (tlctxt @ hdctxt, tlte, tlty, comp_subs (hds @ tls))::tl'

                        ) tl' l                         

                  ) [] l

              )

            | Var x -> (

                if not (vsin x bv) then (

                  let v = fresh_name_list_name (tcgfv.gfv +++ bv) "?V" in
                    tcgfv.gfv <- v ++ tcgfv.gfv;
                    let x1 = fresh_name_list_name (tcgfv.gfv +++ bv) "?T" in
                      tcgfv.gfv <- x1 ++ tcgfv.gfv;
                      let ty1 = Var x1 in
                      let x2 = fresh_name_list_name (tcgfv.gfv +++ bv) "?T" in
                        tcgfv.gfv <- x2 ++ tcgfv.gfv;
                        let ty2 = Var x2 in
                        let sx = (x, Forall (v, ty1, ty2))::[] in

                        let ctxt' = (x2, Type)::(x1, Type)::[] in
                        let ctxt = apply_subs_context ctxt sx bv in
                        let te = apply_subs_term te sx bv in
                        let hd = apply_subs_term hd sx bv in
                        let tl = apply_subs_listterm tl sx bv in
                          
                        let l = termcheck (ctxt' @ ctxt) hd (Some ty1) bv def coercion oracles overload implicite terminaison in
                          
                          List.fold_left (
                            
                            fun tl' hd ->
                              
                              let (hdctxt, hdte, hdty, hds) = hd in

                                
                              let ctxt = apply_subs_context ctxt hds bv in
                              let ctxt' = apply_subs_context ctxt' hds bv in
                              let te = apply_subs_term te hds bv in
                              let tl = apply_subs_listterm tl hds bv in
                              let ty2 = apply_subs_term ty2 hds (v ++ bv) in
                                
                              let ty = (rewrite_term_var_term (alpha_term_vars ty2 (term_fv hdte VarSet.empty)) v hdte) in
                                
                              let l = termcheckapp (hdctxt @ ctxt' @ ctxt) (App (te, hdte::[])) tl ty bv def coercion oracles overload implicite terminaison in
                                
                                List.fold_left (
                                  
                                  fun tl' hd ->
                                    
                                    let (tlctxt, tlte, tlty, tls) = hd in
                                    let hdctxt = apply_subs_context hdctxt tls bv in
                                    let ctxt' = apply_subs_context ctxt' tls bv in
                                      
                                      (tlctxt @ hdctxt @ ctxt', tlte, tlty, comp_subs (sx @ hds @ tls))::tl'
                                        
                                ) tl' l                         
                                  
                          ) [] l

                ) else (

		  let ty' = simpl ty def in
		    if (ty' == ty) then [] else
		      termcheckapp ctxt te args ty' bv def coercion oracles overload implicite terminaison

		  
		  (*
                  printf "prout1!!!!\n%s \\in %s\n" x (string_of_listofvar (VarSet.elements bv));
                  *)
                )
              )

            | _ -> 
		print_error (sprintf "app problem:\n%s: %s\n\n"
			       (string_of_term (App(te,args)) implicite)
			       (string_of_term ty implicite));		  
                []

      )

and termcheckldes ctxt lctxt lcons ltype lbv bv def coercion oracles overload implicite terminaison =
  match (lctxt, lcons, ltype, lbv, terminaison) with
    | ([],[],[],[],[]) -> ([],[],[],[])::[]
    | (hdctxt::tlctxt, hdte::tlte, hdty::tlty, hdbv::tlbv, hdterminaison::tlterminaison) ->(
	(*
        printf "termcheckldes:\n%s|-\n%s: %s\n\n"
          (string_of_listvarterm hdctxt VarMap.empty)
          (string_of_term hdte VarMap.empty)
	  (match hdty with
	     | None -> "??"
	     | Some hdty ->
		 (string_of_term hdty VarMap.empty)
	  );
	*)

        let l = termcheck (hdctxt) hdte hdty (hdbv +++ bv) def coercion oracles overload implicite hdterminaison in
          
	  List.fold_left (
            
            fun tl' hd ->
              
              let (ctxt', hd', ty', s') = hd in
                
              let ctxt = apply_subs_context ctxt s' bv in
              let tlctxt = apply_subs_listcontext tlctxt s' bv in
              let tlte = apply_subs_listterm tlte s' bv in
              let tlty = apply_subs_listoptionterm tlty s' bv in
                
              let l = termcheckldes ctxt tlctxt tlte tlty tlbv bv def coercion oracles overload implicite tlterminaison in
                
                List.fold_left (
                  
                  fun tl' hd ->
                    
                    let (ctxt'', tlc'', ty'', s'') = hd in
                    let ctxt' = apply_subs_context ctxt' s'' bv in
                    let hd' = apply_subs_term hd' s'' bv in
                    let ty' = apply_subs_term ty' s'' bv in
                      
                      (ctxt'' @ ctxt', hd'::tlc'', ty'::ty'', comp_subs (s' @ s''))::tl'
                      
                        
                        
                ) tl' l                
                  
                  
          ) [] l

      )
    | _ -> (* probleme *) print_error "probleme !!!!\n"; []


and termchecklcons ctxt lcons ltype bv def coercion oracles overload implicite terminaison =
  match (lcons, ltype) with
    | ([], []) -> ([],[],[],[])::[]
    | (hdc :: tlc, hdty::tlty) -> (

        let l = termcheck ctxt hdc hdty bv def coercion oracles overload implicite terminaison in

          List.fold_left (

            fun tl' hd ->

              let (ctxt', hd', ty', s') = hd in
                
              let ctxt = apply_subs_context ctxt s' bv in
              let tlc = apply_subs_listterm tlc s' bv in
              let tlty = apply_subs_listoptionterm tlty s' bv in

              let l = termchecklcons ctxt tlc tlty bv def coercion oracles overload implicite terminaison in

                List.fold_left (

                  fun tl' hd ->

                    let (ctxt'', tlc'', ty'', s'') = hd in
                    let ctxt' = apply_subs_context ctxt' s'' bv in
                    let hd' = apply_subs_term hd' s'' bv in
                    let ty' = apply_subs_term ty' s'' bv in
                      
                      (ctxt'' @ ctxt', hd'::tlc'', ty'::ty'', comp_subs (s' @ s''))::tl'                      

                ) tl' l                
                

          ) [] l
      )
    | _ -> (* probleme *) []

and termchecklargs ctxt largs bv def coercion oracles overload implicite terminaison =
  match largs with
    | [] -> ([],[],[])::[]
    | (hd1, hd2) :: tl ->
        let l = termcheck ctxt hd2 (Some Type) bv def coercion oracles overload implicite terminaison in
          
          List.fold_left (

            fun tl' hd ->
              let (ctxt', hd2, _, s') = hd in
                
              let ctxt = apply_subs_context ctxt s' bv in
              let tl = apply_subs_listvarterm tl s' bv in
                
              let l = termchecklargs ((hd1, hd2) :: ctxt' @ ctxt) tl (hd1 ++ bv) def coercion oracles overload implicite terminaison in
                
                List.fold_left (
                  
                  fun tl' hd ->
                    
                    let (ctxt'', tl'', s'') = hd in
                      
                    let ctxt' = apply_subs_context ctxt' s'' bv in
                    let hd2 = apply_subs_term hd2 s'' bv in

                      (ctxt'' @ ctxt', (hd1, hd2):: tl'', comp_subs (s' @ s''))::tl'
                      
                      
                ) tl' l
                  
                  
          ) [] l

(**********************************)
(* term unification using oracles *)
(**********************************)

and termcheckerunification ctxt te1 te2 bv def coercion oracles overload implicite terminaison =
  let te1' = (simpl te1 def) in
  let te2' = (simpl te2 def) in
  (* te1 and te2 must be well-typed *)
  match unification_term te1' te2' bv def with
    | NoMgu ->
	if (term_eq te1' te2' def) then
          Mgu []
	else (
	  (*
	  printf "problem: unification\n%s\n VS \n%s\n\n"
	    (string_of_term te1 implicite)
	    (string_of_term te2 implicite);
	  *)
	  unification_term te1 te2 bv def
          (*NoMgu*)
	)
    | DnkMgu -> 
        (* generalize with a unification that use oracles*)
        
        (* special case: equality *)
        (
          match termcheck ctxt te1' None bv def coercion oracles overload implicite terminaison with
            | [] -> (*printf "oracle NoMgu";*) NoMgu
            | (ctxt1, te1', ty1, s1)::tl ->
              
		let eq = Ind ("eq", ("A", Type) :: ("a", Var "A") :: [], Forall ("b", Var "A", Type), (App (Var "eq", (Var "A")::(Var "a")::(Var "a")::[])) :: []) in
		let prop = App (eq, ty1 :: te1' :: te2' ::[]) in
                  if 
                    termcheckeqoracles ctxt prop bv def coercion oracles overload oracles implicite terminaison 
                  then 
                    Mgu []
                  else
                    unification_term te1 te2 bv def
              
        )

    | Mgu s ->
        Mgu s

and termcheckerunificationlist ctxt l1 l2 bv def coercion oracles overload implicite terminaison =
  match (l1, l2) with
    | ([], []) -> Mgu []
    | (hd1 :: tl1, hd2 :: tl2) -> (
        
        match termcheckerunification ctxt hd1 hd2 bv def coercion oracles overload implicite terminaison with
          | NoMgu -> NoMgu
          | DnkMgu -> DnkMgu
          | Mgu s ->
              let ctxt = apply_subs_context ctxt s bv in
              let tl1 = apply_subs_listterm tl1 s bv in 
              let tl2 = apply_subs_listterm tl2 s bv in 
                match termcheckerunificationlist ctxt tl1 tl2 bv def coercion oracles overload implicite terminaison with
                  | NoMgu -> NoMgu
                  | DnkMgu -> DnkMgu
                  | Mgu s' ->
                      Mgu (comp_subs (s @ s'))
                      

      )
    | _ -> DnkMgu


(******************)
(* Really bad !!! *)
(******************)

and listtypeeq ctxt ty lt bv def coercion oracles overload implicite terminaison =

  List.fold_left (

    fun tl' hd ->
      
      if (term_eq (simpl ty def) (simpl hd def) def) then
        tl'
      else
        None              

  ) (Some ty) lt
  
and listtyunif ctxt ty lt bv def coercion oracles overload implicite terminaison =
  match 
    List.fold_left (
      
      fun tl' hd ->
	
	match tl' with
	  | None -> None
	  | Some s ->
	      (*printf "ty == %s && hd == %s\n" (string_of_term (apply_subs_term ty s bv) implicite) (string_of_term (apply_subs_term hd s bv) implicite);*)
	      match termcheckerunification ctxt (apply_subs_term ty s bv) (apply_subs_term hd s bv) bv def coercion oracles overload implicite terminaison with
		| NoMgu -> None
		| DnkMgu -> None
		| Mgu s' -> Some (comp_subs (s @ s'))
    ) (Some []) lt
  with
    | None -> None
    | Some s ->
	(*intf "result := %s\n" (string_of_term (apply_subs_term ty s bv) implicite);*)
	Some (apply_subs_term ty s bv, s)

		  
		  

(**********************************************************************)
(* Equality of term, through classical equality, or through an oracle *)
(* te1 and te2 must be well-typed                                     *)
(**********************************************************************)

and termcheckeq ctxt te1 te2 ty bv def coercion oracles overload implicite terminaison =
  if (term_eq (simpl te1 def) (simpl te2 def) def) then
    (* the answer got through the *)
    true
  else
    let eq = Ind ("eq", ("A", Type) :: ("a", Var "A") :: [], Forall ("b", Var "A", Type), (App (Var "eq", (Var "A")::(Var "a")::(Var "a")::[])) :: []) in
    let prop = App (eq, ty :: te1 :: te2 ::[]) in
      termcheckeqoracles ctxt prop bv def coercion oracles overload oracles implicite terminaison 

(********************)
(* calls to oracles *)
(********************)      

and termcheckeqoracles ctxt prop bv def coercion oracles overload lo implicite terminaison =
  match lo with
    | [] -> false
    | hd :: tl -> (
        match hd ctxt prop def with
	  | None -> false
	  | Some proof ->
              match termcheck ctxt proof (Some prop) bv def coercion oracles overload implicite terminaison with
		| [] -> termcheckeqoracles ctxt prop bv def coercion oracles overload tl implicite terminaison 
		| _ -> true
      )

(******************)
(*  coercion      *)
(******************)

and termcheckerunification_wtsimpl ctxt te1 te2 bv def coercion oracles overload implicite terminaison =
  (* te1 and te2 must be well-typed *)
  match unification_term te1 te2 bv def with
    | NoMgu ->
        NoMgu
    | DnkMgu -> 
        (* generalize with a unification that use oracles*)
        
        (* special case: equality *)
        (
          match termcheck ctxt te1 None bv def coercion oracles overload implicite terminaison with
            | [] -> NoMgu
          | (ctxt1, te1, ty1, s1)::tl ->
              
              let eq = Ind ("eq", ("A", Type) :: ("a", Var "A") :: [], Forall ("b", Var "A", Type), (App (Var "eq", (Var "A")::(Var "a")::(Var "a")::[])) :: []) in
              let prop = App (eq, ty1 :: te1 :: te2 ::[]) in
                if 
                  termcheckeqoracles ctxt prop bv def coercion oracles overload oracles implicite terminaison 
                then 
                  Mgu []
                else
                  DnkMgu
              
        )
	  
    | Mgu s ->
        Mgu s

(* for coercion we should like no simplication in unification *)

and coerce ctxt te tey ty bv def coercion oracles overload implicite terminaison =
  (*
  printf "look for a coercion: (%s) : --> (%s)\n" 
    (string_of_term (fold te bv def) implicite)
    (string_of_term (fold ty bv def) implicite); flush stdout;
  *)
  let te = (fold te bv def) in 
  let ty = (fold ty bv def) in

  List.fold_left (
    
    fun acc hd ->
      
      let (te', ty') = hd in
	(*
	printf "Choosen: (%s: %s) [%d]\n"
	  (string_of_term te' implicite)
	  (string_of_term ty' implicite)
	  i;
	*)
      let ty' = alpha_term_vars ty' (bv +++ tcgfv.gfv) in

      let (hyp, ccl) = decomp_foralls ty' in

	if (List.length hyp <= 0) then
	  acc
	else 
	  
	  let (hyp, hypt) = (nth_head (List.length hyp - 1) hyp, nth_tail (List.length hyp - 1) hyp) in

	    tcgfv.gfv <- tcgfv.gfv +++ (list2varset (list_proj1 hyp));

	    match hypt with
	      | (hd1, hd2) :: [] -> (
		  (*
		    printf "(%s\n\tVs\n%s)\n"
		    (string_of_term ccl implicite)
		    (string_of_term ty implicite);
		  *)
		  
		  match termcheckerunification_wtsimpl ctxt ccl ty bv def coercion oracles overload implicite terminaison with
		    | NoMgu -> acc
		    | DnkMgu -> acc
		    | Mgu s ->                
			(*
			  printf "subs:= %s\n" (string_of_listvarterm (comp_subs s) implicite);
			*)
			let s = comp_subs s in
			  
			let hd2 = apply_subs_term hd2 s bv in
			let te = apply_subs_term te s bv in
			let ctxt = apply_subs_context ctxt s bv in
			  (*
			    printf "%s|-\n%s: %s\n\n\n" 
			    (string_of_listvarterm ctxt implicite)
			    (string_of_term te implicite)
			    (string_of_term hd2 implicite);
			  *)
			let l = termcheck ctxt te (Some hd2) (bv +++ (list2varset (list_proj1 hyp))) def (list_remove hd coercion) oracles overload implicite terminaison in
			  
			  acc @ (
			    

			    List.fold_left (

			      fun acc hd ->

				let  (ctxt1, te1, ty1, s1) = hd in

				  acc @ (

				    let largs = apply_subs_listterm (list_name2list_var (list_proj1 hyp)) s bv in
				      
				      (* ca c'est un peu ole ole *)
				      (ctxt1, App (te', largs @ te1::[]), ty, comp_subs (s @ s1))::[]

				  )


			    ) [] l			  
			      
			  )

		)
	      | _ -> acc

  ) [] coercion 

(************************)
(* Destruction of cases *)
(************************)

and destruct_cases ctxt te ty args n ldes lcons ind_name ind_args ind_ty ind_lcons bv def coercion oracles overload implicite terminaison =
  match (lcons, ldes) with
    | ([], []) -> (
        match ldes with
          | [] -> Some ([], [], [], [], [], [], [])
          | _ -> print_debug "destruct_case1\n"; None
      )
    | (hdc :: tlc, hdd :: tld) -> (
	let ind = (Ind (ind_name, ind_args, ind_ty, ind_lcons)) in

	(*printf "\n\nfold1 : %s ==>\n" (string_of_term ind implicite);
	  
          let ind = fold (Ind (ind_name, ind_args, ind_ty, ind_lcons)) bv def in
	  printf "%s ...\n\n" (string_of_term ind implicite);
        *)

	let hdc = (alpha_term_vars (largs_foralls (rewrite_term_var_term hdc ind_name (Ind (ind_name, ind_args, ind_ty, ind_lcons))) ind_args) ((listvarterm2varset ctxt) +++ (listterm_fv args VarSet.empty) +++ bv)) in
	  
	(*printf "\n\nfold2 : %s ==>\n" (string_of_term hdc implicite);*)
	  
	let hdc = fold hdc (ind_name ++ bv) def in
	  
	(*printf "%s ...\n\n" (string_of_term hdc implicite);*)
	  
        let (hdcqv, hdccon) = (decomp_foralls hdc) in 
        let (hdcconfct, hdcconargs) = (decomp_app hdccon) in 

          match termcheckerunificationlist ctxt hdcconargs args
            (*fv*)
            (VarSet.diff bv (listterm_fv args VarSet.empty))
            def coercion oracles overload implicite terminaison 
          with
            | NoMgu -> (

		(*printf "destructor %d useless\n" n;*)
		match destruct_cases ctxt te ty args (n+1) tld tlc ind_name ind_args ind_ty ind_lcons bv def coercion oracles overload implicite terminaison with
                  | None -> None
                  | Some (l1, l2, l3, l4, l5, l6, s'') ->
		      Some (l1, l2, l3, l4, n::l5, l6, s'')
	      )
            | a ->
		
                match destruct_cases ctxt te ty args (n+1) tld tlc ind_name ind_args ind_ty ind_lcons bv def coercion oracles overload implicite terminaison with
                  | None -> None
                  | Some (l1, l2, l3, l4, l5, l6, s'') ->
                      
		      (*
                        printf "(%s Vs %s := %s)\n" (string_of_listterm hdcconargs implicite) (string_of_listterm args implicite) (
                        match a with
                        | Mgu s -> (string_of_listvarterm s implicite)
                        | NoMgu -> "NoMgu :D"
                        | DnkMgu -> "DnkMgu :D"
                        ); 
                      *)
                      let s = (
                        match a with
                          | Mgu s -> (comp_subs s)
                          | _ -> []
                      ) in
                        
                      let ctxt = (rev hdcqv) @ ctxt in                        
                      let ctxt = apply_subs_context ctxt s VarSet.empty in
                      let hdd = (alpha_term_vars hdd (listvarterm2varset ctxt)) in    
		      let p = (app_nf (App (Cons (n,ind), apply_subs_listterm (list_name2list_var (list_proj1 hdcqv)) s VarSet.empty))) in

		      (*let p = (app_nf (App (Cons (n,(Ind (ind_name, ind_args, ind_ty, ind_lcons))), apply_subs_listterm (list_name2list_var (list_proj1 hdcqv)) s VarSet.empty))) in*)

                      let ctxt = rewrite_context_term_term ctxt te p (*fv*) VarSet.empty def in 
			
                      let ty = rewrite_term_term_term ty te p (*fv*) VarSet.empty def in
                      let ty = apply_subs_term ty s VarSet.empty in
                      let hdd = rewrite_term_term_term hdd te p VarSet.empty def in
                      let hdd = apply_subs_term hdd s VarSet.empty in
                      let (hddlam,_) = decomp_nlambdas hdd (List.length hdcqv) in
                      let m_args = apply_subs_listterm (list_name2list_var (list_proj1 hdcqv)) s VarSet.empty in
                        
                      let lt1 = (
                        rev (list_proj2 (rewrite_context_term_term (apply_subs_context (rev hdcqv) s VarSet.empty) te p VarSet.empty def))
                      ) in
                      let lt2 = (list_proj2 hddlam) in
                        (*
                          printf "%s Vs %s\n"
                          (string_of_listterm lt1 VarMap.empty)
                          (string_of_listterm lt2 VarMap.empty);
                        *)

                      let s' = (

                        
                        match termcheckerunificationlist ctxt lt2 lt1
                          (*fv*)
                          (VarSet.diff bv (listterm_fv args VarSet.empty))
                          def coercion oracles overload implicite terminaison with
                            | Mgu s -> s
                            | _ -> []
                                
                      ) in

		      let new_terminaison = (

			let (formula, listdec) = terminaison in

			  match (sum_term_size_arith m_args def, term_size_arith te def) with
			    | (Some e1, Some e2) ->
				
				(Band 
				   (formula, 
				    Band (
				      Beq (Nplus (Ncons 1, e1), e2), 
				      list_term_size_arith_gt0 m_args def
				    )
				   )
				   , 
				 listdec
				)

			    | _ -> 

				(*printf "problem with ([%s], [%s])\n\n" (string_of_listterm m_args implicite) (string_of_term te implicite);*)
				terminaison
			  
		      ) in
  
		      let hdd =

			List.fold_left (

			  fun acc hd ->
			    
			    match acc with
			      | Lambda (x,ty,te) ->
				  
				  rewrite_term_var_term te x hd 

			      | _ -> print_error (sprintf "Should never be there:%s / %s !!\n\n" (string_of_term hdd VarMap.empty) (string_of_listterm m_args VarMap.empty)); 
				  Type

			) hdd m_args in

			(*
			printf "%s --> %s\n\n" (string_of_term te VarMap.empty) (string_of_term p VarMap.empty);
                          printf "%s|-\n%s: %s\n"
                          (string_of_listvarterm ctxt VarMap.empty)
                          (string_of_term hdd VarMap.empty)
                          (string_of_term ty VarMap.empty);
                          printf "[%s]\n\n" (string_of_listvarterm s VarMap.empty);
			*)

                        Some (ctxt::l1, hdd::l2, ty::l3, (rev (nth_head (List.length hdcqv) ctxt))::l4, l5, new_terminaison::l6, comp_subs (s'' @ s'))

      )
    | _ -> None
;;

