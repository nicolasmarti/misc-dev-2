open Term;;
open Env;;
open Reduction;;
open Universe;;
open Printf;;
open Listext;;
open Pprinter;;
open Definition;;

(* unification exception *)

exception UnificationFail
;;

exception UnificationUnknown
;;

type unification =
  | Mgu of term
  | NoMgu
  | DnkMgu
;;

(* unification  *)
let rec unification_term (t1: term) (t2: term) (st: typechecker_state): term =
    try (
      match (t1, t2) with
	| (TType alpha, TType beta) -> 
	    st.univ_constraint <- (UEq (alpha, beta))::st.univ_constraint;
	    TType alpha
	| (TCste c1, TCste c2) -> (
	    if (c1 = c2) then
	      TCste c1
	    else
	      raise UnificationFail
	  )
	| (TPrim p1, TPrim p2) -> (
	    if p1#equal p2 then
	      TPrim p1
	    else
	      raise UnificationFail
	  )
	| (TVar v1, t2) -> (
	    if FreeVarSet.exists (fun hd -> hd = v1) st.sv && not (FreeVarSet.exists (fun hd -> hd = v1) (fv t2 (List.length st.qv))) then (
	      tcst_applysubst st (FreeVarMap.add v1 t2 FreeVarMap.empty);
	      t2
	    )	    
	    else
	      match t2 with
		| TVar v2 -> 
		    if FreeVarSet.exists (fun hd -> hd = v2) st.sv then (
		      tcst_applysubst st (FreeVarMap.add v2 t1 FreeVarMap.empty);
		      t1
		    ) else 
		      if v1 = v2 then
			TVar v1 
		      else
			raise UnificationFail	      		      
		| _ -> raise UnificationFail	      
	  )
	| (t1, TVar v2) -> (
	    if FreeVarSet.exists (fun hd -> hd = v2) st.sv && not (FreeVarSet.exists (fun hd -> hd = v2) (fv t1 (List.length st.qv))) then (
	      tcst_applysubst st (FreeVarMap.add v2 t1 FreeVarMap.empty);
	      t1
	    ) else raise UnificationFail	      		      
	  )	    
	| (TLet ((n1, t11, ty1), t12), TLet ((n2, t21, ty2), t22)) -> (
	    let t1 = unification_term t11 t21 st in
	    let ty = unification_term ty1 ty2 st in
	    let _ = tcst_pushterm st t1 in
	      tcst_pushqv st n1 ty Explicite;
	      let t2 = unification_term t12 t22 st in
	      let ((_, ty, _), t2) = tcst_popqv st t2 in
	      let t1 = tcst_popterm st in
		TLet ((n1, t1, ty), t2)
	  )
	| (TLambda ((x1, ty1, n1), te1), TLambda ((x2, ty2, n2), te2)) -> (
	    if n1 = n2 then (
	      
	      let ty = unification_term ty1 ty2 st in
		tcst_pushqv st x1 ty n1;
		let te = unification_term te1 te2 st in
		let ((_, ty, _), te) = tcst_popqv st te in
		  TLambda ((x1, ty, n1), te)
		    
	    ) else raise UnificationFail
	  )
	| (TForall ((x1, ty1, n1), te1), TForall ((x2, ty2, n2), te2)) -> (
	    if n1 = n2 then (
	      
	      let ty = unification_term ty1 ty2 st in
		tcst_pushqv st x1 ty n1;
		let te = unification_term te1 te2 st in
		let ((_, ty, _), te) = tcst_popqv st te in
		  TForall ((x1, ty, n1), te)
		    
	    ) else raise UnificationFail
	  )
	| (TConstr (i1, t1), TConstr (i2, t2)) -> (
	    if (i1 = i2) then (
	      let t = unification_term t1 t2 st in
		tcst_subst st (TConstr (i1, t))
	    ) else raise UnificationFail
	  )
	| (TApp (fct1, args1), TApp (fct2, args2)) -> (
	    if (List.length args1 = List.length args2) then (	      
	      let fct = unification_term fct1 fct2 st in
	      let args = List.map (fun (hd1, hd2) -> 
				     if (snd hd1 = snd hd2) then
				       (unification_term (fst hd1) (fst hd2) st, snd hd1)
				     else
				       raise UnificationFail
				  ) (List.combine args1 args2) in
		tcst_subst st (TApp (fct, args))		
	    ) else (
	      let fct = unification_term fct1 fct2 st in
	      (* here we might need to do some saving of environment ... *)
	      (* in this case we can try to split the App in two *)
	      if List.length args1 < List.length args2 then (
		let (args21, args22) = nth_split (List.length args2 - List.length args1) args2 in
		let t2' = TApp (TApp (fct, args21), args22) in
		  unification_term t1 t2' st
	    ) else (
		let (args11, args12) = nth_split (List.length args1 - List.length args2) args1 in
		let t1' = TApp (TApp (fct, args11), args12) in
		  unification_term t1' t2 st 
	      )
	    )

	  )
	| (TMatch (t1, ldes1, ty1), TMatch (t2, ldes2, ty2)) -> (
	    let t = unification_term t1 t2 st in
	    let ty = unification_term ty1 ty2 st in
	    let ldes = Array.mapi (fun i hd -> 
				     match (hd, ldes2.(i)) with
				       | (None, None) -> None
				       | (Some hd1,  Some hd2) ->
					   Some (unification_term hd1 hd2 st)
				       | _ -> raise UnificationFail
				  ) ldes1 in
	      tcst_subst st (TMatch (t, ldes, ty))
	  )
	| (TPhi (x1, args1, ty1, pt1, body1), TPhi (x2, args2, ty2, pt2, body2)) -> (
	    let args = List.map (fun ((hd11, hd12, hd13), (hd21, hd22, hd23)) ->
				   if (hd13 = hd23) then (
				     let ty = unification_term hd12 hd22 st in
				       tcst_pushqv st hd11 ty hd13;
				       (hd11, ty, hd13)
				   ) else raise UnificationFail
				) (List.combine args1 args2) in
	    let ty = unification_term ty1 ty2 st in
	    let _ = tcst_pushterm st ty in
	    tcst_pushqv st x1 (List.fold_right 
				 (fun hd acc ->
				    TForall (hd, acc)
				 )
				 args
				 ty
			      ) Explicite;
	    let body = unification_term body1 body2 st in
	    let _ = tcst_popqv2 st in
	    let ty = tcst_popterm st in
	    let args = List.rev (List.map (fun _ -> tcst_popqv2 st) args) in
	      TPhi (x1, args, ty, pt1, body)
	  )
	| (TInd (x1, args1, ty1, lcons1), TInd (x2, args2, ty2, lcons2)) -> (
	    let args = List.map (fun ((hd11, hd12, hd13), (hd21, hd22, hd23)) ->
				   if (hd13 = hd23) then (
				     let ty = unification_term hd12 hd22 st in
				       tcst_pushqv st hd11 ty hd13;
				       (hd11, ty, hd13)
				   ) else raise UnificationFail
				) (List.combine args1 args2) in
	    let ty = unification_term ty1 ty2 st in
	    let _ = tcst_pushterm st ty in
	    tcst_pushqv st x1 (List.fold_right 
				 (fun hd acc ->
				    TForall (hd, acc)
				 )
				 args
				 ty
			      ) Explicite;
	    let lcons = (if (Array.length lcons1 = Array.length lcons2) then
			   (Array.mapi (fun i hd -> unification_term hd lcons2.(i) st) lcons1)
			 else
			   raise UnificationFail
			) in
	    let _ = tcst_popqv2 st in
	    let ty = tcst_popterm st in
	    let args = List.rev (List.map (fun _ -> tcst_popqv2 st) args) in
	      TInd (x1, args, ty, lcons)
	  )
	| (TCste c1, t2) -> (

	    try 
	      match finddef c1 st.def with
		| None -> raise UnificationFail
		| Some (_ , (te, _, _)) -> let _ = unification_term te t2 st in TCste c1
	    with
	      | UnificationFail -> raise UnificationFail

	  )

	| (t1, TCste c2) -> (

	    try 
	      match finddef c2 st.def with
		| None -> raise UnificationFail
		| Some (_ , (te, _, _)) -> let _ = unification_term t1 te st in TCste c2
	    with
	      | UnificationFail -> raise UnificationFail

	  )

	| (_, _) -> (
	    
	    printf "Unification Case Not Yet Implemented\n";
	    pprintterm t1 true;
	    printf "Vs\n";
	    pprintterm t2 true;
	    printf "\n";
	    
	    raise UnificationFail
	  )

    ) with
      | UnificationFail -> (
	  (* in this case look if we could try 
	     a beta reduction/eta expension 
	  *)

	  (* this function return None if the term cannot be betared
	     else we return a Some of the betareded term
	  *)
	  
	  let dobetared te = (
	    let te' = reduction_unification st te in
	      if (te' = te) then None else Some te'		
	  ) in
	    match (dobetared t1, dobetared t2) with
	      | (None, None) -> (
		  (*
		  printf "Unification Failed\n";
		  pprintterm t1 true;
		  printf "Vs\n";
		  pprintterm t2 true;
		  printf "\n";
		  *)
		  raise UnificationFail
		)
	      | (Some t1, None) -> unification_term t1 t2 st
	      | (None, Some t2) -> unification_term t1 t2 st
	      | (Some t1, Some t2) -> unification_term t1 t2 st

	)
      | UnificationUnknown ->
	  raise UnificationUnknown
      | MshiftException ->
	  (*
	  printf "Unification Failed: Shifting problem\n";
	  pprintterm t1 true;
	  printf "Vs\n";
	  pprintterm t2 true;
	  printf "\n";
	  *)
	  raise UnificationFail
      | e -> (
	  printf "unknown exception in unification: "; 
	  printbox (token2box (Box (term2token t1 false (List.map (fun (x, _, _) -> x) st.qv))) 40 2);
	  printbox (token2box (Box (term2token t2 false (List.map (fun (x, _, _) -> x) st.qv))) 40 2);
	  raise e
	)
(* level correspond to the level of quantified variable *)
and unification (t1: term) (t2: term) (st: typechecker_state) : unification =
  (* TODO: need to save the environment *)
  try (
    (* TODO: might need to rewrite the term with the substitution *)
    let t = unification_term t1 t2 st in
      Mgu t
  ) with
    (* TODO: need to reload the environment *)
    | UnificationUnknown -> DnkMgu
    | UnificationFail -> NoMgu
;;



