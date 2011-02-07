open Term;;
open Env;;
open Universe;;
open Definition;;
open Reduction;;
open Pprinter;;
open Printf;;
open Unification;; 
open Listext;;

exception TermCheckFailure of string;;

let rec termcheck (st: typechecker_state) (te: term) (ty: term) : (term * term) =
  (*printf "typecheck: "; printbox (token2box (Box (term2token te false (List.map (fun (x, _, _) -> x) st.qv))) 40 2); printf ": "; printbox (token2box (Box (term2token ty false (List.map (fun (x, _, _) -> x) st.qv))) 40 2); printf "\n"; *)
  let (reste, resty) = (
    infer st te 
  ) in
    init_sv st;
    match unification resty ty st with
      | Mgu t -> (apply_substitution_term reste st.s, apply_substitution_term ty st.s)		 
      | _ -> (
	  (*
	  printf "typecheck problem error: "; printbox (token2box (Box (term2token te false (List.map (fun (x, _, _) -> x) st.qv))) 40 2);
	  printf "infered: "; printbox (token2box (Box (term2token resty false (List.map (fun (x, _, _) -> x) st.qv))) 40 2);
	  printf "annotation: "; printbox (token2box (Box (term2token ty false (List.map (fun (x, _, _) -> x) st.qv))) 40 2);
	  *)
	  raise (TermCheckFailure "termcheck: error in unification")
	)

and infer (st: typechecker_state) (te: term) : (term * term) =
  let (nqv, ntstck) = (List.length st.qv, List.map List.length st.term_storage) in
  (*printf "infer: "; printbox (token2box (Box (term2token te false (List.map (fun (x, _, _) -> x) st.qv))) 40 2); printf "\n";*)
  let (te, ty) =
    match te with
      | TType u -> infer_TType st u
      | TCste c -> infer_TCste st c
      | TPrim p -> infer_TPrim st p 
      | TVar v -> infer_TVar st v
      | TLet (l, t) -> infer_TLet st l t
      | TLambda (b, body) -> infer_TLambda st b body
      | TForall (b, body) -> infer_TForall st b body
      | TApp (fct, args) -> infer_TApp st fct args
      | TInd (x, l, ty, lcons) -> infer_TInd st x l ty lcons 
      | TPhi (x, l, ty, tp, body) -> infer_TPhi st x l ty tp body
      | TMatch (te, ldes, ty) -> infer_TMatch st te ldes ty
      | TConstr (i, te) -> infer_TConstr st i te 
      | t -> raise (Failure (String.concat " " ["not supported case"; term_head_string t]))
  in
  let (nqv', ntstck') = (List.length st.qv, List.map List.length st.term_storage) in
    if (nqv = nqv' && ntstck' = ntstck) then (te, ty) else raise (Failure "Final countdown")

and infer_TType (st: typechecker_state) (u: univ_level) : (term * term) =
  (TType u, TType (Succ u))

and infer_TCste (st: typechecker_state) (c: name) : (term * term) =
  match finddef c st.def with
    | None -> raise (TermCheckFailure (
		       String.concat " " (("no such definition:")::c::[])
		     )
		    )
    | Some (n , (te, ty, nature)) -> (TCste c, ty)

and infer_TPrim (st: typechecker_state) (p: term primitive) : (term * term) =
  (TPrim p, p#get_type)

and infer_TVar (st: typechecker_state) (v: int) : (term * term) =
  try (
    infer st (FreeVarMap.find v st.s)
  )
  with
    | not_found -> (tcst_varval st v, tcst_vartype st v)
    
and infer_TLet (st: typechecker_state) (l: name * term * term) (t: term) : (term * term) =
  let (x, te, ty) = l in
    (* FIXME: should check that ty is of type type --> need to build a special function *)
  let (te, ty) = termcheck st te ty in

  let _ = tcst_pushterm st te in
    tcst_pushqv st x ty Explicite;

    let (te2, ty2) = infer st t in

    let (x, ty, _) = tcst_popqv2 st in
    let te = tcst_popterm st in
      (TLet ((x, te, ty), te2), shift_var ty2 (-1))

and infer_TLambda (st: typechecker_state) (b: binder) (body: term) : (term * term) =
  let (x, ty, n) = b in
    (* FIXME: should check that ty is of type type --> need to build a special function *)
  let (ty, _) = infer st ty in
    tcst_pushqv st x ty n;
    let (body, bodyty) = infer st body in
    let (x, ty, _) = tcst_popqv2 st in
      (TLambda ((x, ty, n), body), TForall ((x, ty, n), bodyty))

and infer_TForall (st: typechecker_state) (b: binder) (body: term) : (term * term) =
  let (x, ty, n) = b in
    (* FIXME: should check that ty is of type type --> need to build a special function *)
  let univ1 = tcst_freshuniv st in
  let (ty, _) = termcheck st ty (TType univ1) in
    tcst_pushqv st x ty n;
    let univ2 = tcst_freshuniv st in
    let (body, _) = termcheck st body (TType univ2) in
    let (x, ty, _) = tcst_popqv2 st in
      (TForall ((x, ty, n), body), TType (Max [univ1; univ2]))

and infer_TApp (st: typechecker_state) (fct: term) (args: (term * nature) list) : (term * term) =

  
  let (fte, fty) = infer st fct in
  let _ = tcst_pushterm st fte in
  let _ = tcst_pushterm st fty in

    
  let l = Listext.fold_left2 (
    fun acc (arg, n) tl ->
      let fty = tcst_popterm st in
      let ((x, ty, n'), te) = (match reduction_checker st fty with
				 | TForall (b, te) -> (b, te)
				 | _ -> raise (Failure "infer_TApp: not a forall")
			      ) in
	if (n' = Hidden && n != n') then (
	  let fv = tcst_add_fv st in
	  let _ = tcst_pushterm st fty in 
	    (acc, (TVar fv, Hidden)::(arg, n)::tl)
	) else (
	  if (n != n') then raise (Failure "infer_TApp: wrong arg nature")
	  else (

	    let _ = tcst_pushterm st (TForall ((x, ty, n'), te)) in

	    let (argte, argty) = termcheck st arg ty in
	      
	    let ((x, ty, n'), te) = (match tcst_popterm st with
				       | TForall (b, te) -> (b, te)
				       | _ -> raise (Failure "infer_TApp: not a forall")

	    ) in


	      let s = FreeVarMap.add 0 (shift_var argte 1) FreeVarMap.empty in
	      let t2 = apply_substitution_term te s in

	      let inferedty = shift_var t2 (-1) in

		
	      let _ = tcst_pushterm st $ apply_substitution_term argte st.s in
	      let _ = tcst_pushterm st $ apply_substitution_term inferedty st.s in
		(n::acc, tl)
	  )
	)		  
  ) [] args in
  let ty = tcst_popterm st in
  let l = 
    List.fold_right (
      fun hd acc ->
	
	let te = tcst_popterm st in
	  (te, hd) :: acc
	    
    ) (List.rev l) [] in
  let fct = tcst_popterm st in
    (TApp (fct, l) , ty)

and infer_TInd (st: typechecker_state) (x: string) (largs: binders) (ty: term) (lcons: term array) : (term * term) =
  List.map (
    fun (x, ty, n) ->
      let univ1 = tcst_freshuniv st in
      let (ty, _) = termcheck st ty (TType univ1) in
	tcst_pushqv st x ty n
  ) largs;
  let univ = tcst_freshuniv st in
  let (tyte, _) = termcheck st ty (TType univ) in
  let _ = tcst_pushterm st ty in
  let (_, xty) = List.fold_right (
    fun (x, _, n) (i, te) ->
      (i + 1, TForall ((x, shift_var_term ((fun (_, x, _) -> x) (List.nth st.qv i)) (i + 1) (List.length largs), n), te))		  
  ) largs (0, shift_var_term tyte (List.length largs) (List.length largs)) in		
    tcst_pushqv st x xty Explicite;	
    
    Array.fold_left (
      fun acc hd ->
	let univ = tcst_freshuniv st in	  
	let (hdte, hdty) = termcheck st hd (TType univ) in
	let _ = tcst_pushterm st hdte in
	  ()
    ) () lcons;
    
    let lcons' = Array.fold_right (
      fun _ acc ->
	let te = tcst_popterm st in
	  te :: acc
    ) lcons [] in

    let lcons = Array.of_list lcons' in

    let _ = tcst_popqv2 st in
      
    let ty' = tcst_popterm st in

    let largs' = List.fold_left (
      fun acc _ ->
	let te = tcst_popqv2 st in
	  acc @ te::[]
    ) [] largs in
      
    let fty = List.fold_right (
      fun hd acc ->
	TForall (hd, acc)
    ) largs'  ty' in
      
      (* and return *)
      (TInd (x, largs', ty', lcons), fty)

and infer_TPhi (st: typechecker_state) (x: string) (largs: binders) (ty: term) (tp: terminaison_pattern) (body: term) : (term * term) =
  List.map (
    fun (x, ty, n) ->
      let univ1 = tcst_freshuniv st in
      let (ty, _) = termcheck st ty (TType univ1) in
	tcst_pushqv st x ty n
  ) largs;
  let univ = tcst_freshuniv st in
  let (tyte, _) = termcheck st ty (TType univ) in
  let tycoo = tcst_pushterm st ty in
  let (_, xty) = List.fold_right (
    fun (x, _, n) (i, te) ->
      (i + 1, TForall ((x, shift_var_term ((fun (_, x, _) -> x) (List.nth st.qv i)) (i + 1) (List.length largs), n), te))		  
  ) largs (0, shift_var_term tyte (List.length largs) (List.length largs)) in		
    tcst_pushqv st x xty Explicite;	
    
    let (bodyte, bodyty) = termcheck st body (tcst_getterm st tycoo) in

    let _ = tcst_popqv2 st in
      
    let ty' = tcst_popterm st in

    let largs' = List.fold_right (
      fun _ acc ->
	let te = tcst_popqv2 st in
	  te::acc
    ) largs [] in
      
    let fty = List.fold_right (
      fun hd acc ->
	TForall (hd, acc)
    ) largs'  ty' in
      
      (* and return *)
      (TPhi (x, largs', ty', tp, bodyte), fty)

and infer_TConstr (st: typechecker_state) (i: int) (te: term) : (term * term) =
  let (tete, tety) = infer st te in
    match reduction_checker st tete with
      | TInd (x, iargs, ty, lcons) -> (
	  TConstr (i, tete), 
	  comp_forall 
	    iargs 
	    (shift_var 
	       (apply_substitution_term  lcons.(i) (FreeVarMap.add 0 tete FreeVarMap.empty)) 
	       (-1)
	    )
	)
      | t -> printbox (token2box (Box (term2token t false [])) 40 2); raise (Failure "infer_TConstr: not an inductive")


and infer_TMatch (st: typechecker_state) (te: term) (ldes: (term option) array) (ty: term) : (term * term) =
  (* infer the destructed term and the inference type *)
  let (tete, tety) = infer st te in
  let cte = tcst_pushterm st tete in
  let univ = tcst_freshuniv st in
  let (tyte, _) = termcheck st ty (TType univ) in
  let cty = tcst_pushterm st tyte in

  (* grab the inductive pattern *)
  let ((x, iargs, ty, lcons), args) = (match reduction_checker st tety with
					 | TInd (x, iargs, ty, lcons) -> ((x, iargs, ty, lcons), [])
					 | TApp (TInd (x, iargs, ty, lcons), args) -> ((x, iargs, ty, lcons), List.map fst args)
					 | _ -> raise (Failure "infer_TMatch: not an inductive")
				      ) in
  let ind = TInd (x, iargs, ty, lcons) in
  let ind = tcst_pushterm st ind in
  let indarg = List.map (fun hd -> tcst_pushterm st hd) args in

  (* loop over destructor *)
  let ldes = Array.mapi (fun i hd ->


			   (* copy the environment *)

			     match hd with
			       | None -> (
				   (* we should have a NoMgu *)
				   None
				 )
			       | Some des -> (

				   (*
				   printf "-----------------------------------------------------------------\n";
				   printbox (token2box (env2token st) 40 2); printf "|-\n\n\n";
				   *)

				   let nb_args = (List.length iargs) + List.length (fst (decomp_forall lcons.(i))) in
				   let (bs, body) = decomp_lambda des in
				   let (bs, body) = (nth_head nb_args bs, comp_lambda (nth_tail nb_args bs) body) in

				   let _ = List.map (fun (hd1, hd2, hd3) -> tcst_pushqv st hd1 hd2 hd3) bs in
				     
				   (*
				   printbox (token2box (env2token st) 40 2); printf "|-\n\n\n";
				     printf "args := %d\n\n" (List.length bs);
				   *)
				     
				   let mte = TApp (TConstr (i, tcst_getterm st ind), List.map (fun hd -> 
												  let n = tcst_qvnature st hd in
												    (TVar hd, n)
											       ) (List.rev $ iota 0 (nb_args - 1))) in 
				     (*
				     printf "-----------------------------------------------------------------\n";
				     printbox (token2box (env2token st) 40 2); printf "|-\n";
				     printbox (token2box (Box (term2token mte false (List.map (fun (x, _, _) -> x) st.qv))) 40 2); printf ":?\n";
				     *)
				   let (mte, mty) = infer st mte in
				     (*
				     printf "-----------------------------------------------------------------\n";
				     printbox (token2box (env2token st) 40 2); printf "|-\n";
				     printbox (token2box (Box (term2token mte false (List.map (fun (x, _, _) -> x) st.qv))) 40 2); printf ":"; printbox (token2box (Box (term2token mty false (List.map (fun (x, _, _) -> x) st.qv))) 40 2);
				   				       
				     printf "-----------------------------------------------------------------\n\n\n";
				     *)
				   let ((x', iargs', ty', lcons'), args') = (match reduction_checker st mty with
									       | TInd (x, iargs, ty, lcons) -> ((x, iargs, ty, lcons), [])
									       | TApp (TInd (x, iargs, ty, lcons), args) -> ((x, iargs, ty, lcons), List.map fst args)
									       | _ -> raise (Failure "infer_TMatch: not an inductive")
									    ) in
				   let valid = List.fold_left (fun acc hd -> 
								 if acc then (
								   let hd1 = tcst_subst st $ fst hd in
								   let hd2 = tcst_subst st $ snd hd in
								     init_sv st;
								     
								     st.sv <- FreeVarSet.union (fv hd1 0) st.sv;
								     st.sv <- FreeVarSet.union (fv hd2 0) st.sv;
								     
								     (*
								     printbox (token2box (env2token st) 40 2); printf "|-\n";
								     printbox (token2box (Box (term2token hd2 false (List.map (fun (x, _, _) -> x) st.qv))) 40 2); printf "VS\n";
								     printbox (token2box (Box (term2token hd1 false (List.map (fun (x, _, _) -> x) st.qv))) 40 2); printf "\n";
								     *)

								     match unification hd2 hd1 st with
								       | Mgu t -> true
								       | DnkMgu -> true
								       | NoMgu -> (									   
									   (*printf "false!!\n\n";*)
									   false
									 )
								 ) else false
							      ) true (List.combine (List.map (fun hd -> tcst_getterm st hd) indarg) args') in
				     if not valid then (
				       
				       let _ = List.map (fun (hd1, hd2, hd3) -> tcst_popqv2 st) bs in
					 None				       

				     ) else (

				       (*
				       printf "\n\n valid body(%d): " i; printbox (token2box (Box (term2token body false (List.map (fun (x, _, _) -> x) st.qv))) 40 2); printf ": "; printbox (token2box (Box (term2token (tcst_getterm st cty) false (List.map (fun (x, _, _) -> x) st.qv))) 40 2); printf "\n"; 				       			       
				       *)

				       let (bodyte, bodyty) = termcheck st body (tcst_getterm st cty) in
					 (*
					 printf "\n\n termcheck body(%d): " i; printbox (token2box (Box (term2token bodyte false (List.map (fun (x, _, _) -> x) st.qv))) 40 2); printf ": "; printbox (token2box (Box (term2token bodyty false (List.map (fun (x, _, _) -> x) st.qv))) 40 2); printf "\n";
					 *)
				       let res = List.fold_right (fun hd acc ->
								    let (b, body) = tcst_popqv st acc in
								      TForall (b, body)
								 ) bs bodyte in
					 
					 Some res

				     )
				       
				 )
			) ldes in

  let _ = List.map (fun hd -> tcst_popterm st) args in
  let _ = tcst_popterm st in
  let ty = tcst_popterm st in
  let te = tcst_popterm st in
    (TMatch (te, ldes, ty), ty)


;;
