open Term;;
open Env;;
open Definition;;
open Printf;;
open Universe;;
open Pprinter;;

(* reduction datastructure *)

type strategy = 
  | Lazy 
  | Eager;;

type interp_state = {
  strat: strategy;
  beta: bool;
  betastrong: bool;
  delta: bool;
  deltastrong: bool;
  iota: bool;
  deltaiotaweak: bool;
  zeta: bool;
  eta: bool;
};;
    
exception ReductionCannotBePerformed of string;;
exception ReductionCaseNotSupported of term;;
exception DeltaIotaException;;

(* state constructor for unification *)
let exec_st_unif () = {
  strat = Lazy;
  beta = true;
  betastrong = true;
  delta = true;
  deltastrong = false;
  iota = true;
  deltaiotaweak = false;
  zeta = true;
  eta = true;
};;

let exec_st_checker () = {
  strat = Lazy;
  beta = true;
  betastrong = true;
  delta = true;
  deltastrong = true;
  iota = true;
  deltaiotaweak = false;
  zeta = true;
  eta = true;
};;



let rec reduction_unification (st: typechecker_state) (t: term) : term = 
  let s = exec_st_unif () in 
    reduction st s t
and reduction_checker (st: typechecker_state) (t: term) : term = 
  let s = exec_st_checker () in 
    reduction st s t
and reduction (st: typechecker_state) (s: interp_state) (t: term) : term = 
  let t = 
    try 
      reduction_loop st s t 
    with
      | DeltaIotaException -> t
      | ReductionCaseNotSupported te -> printf "cannot exec: %s\n" (term_head_string te); raise (ReductionCaseNotSupported te)
  in
  let t = apply_substitution_term t st.s in
(*  let b = env2token st in
    printbox (token2box b 40 2);    
*)
    t    
and reduction_aliase (st: typechecker_state) (s: interp_state) (v: int) : term = 
  try 
    let t = FreeVarMap.find v st.s in
    let t = reduction_loop st s t in
      st.s <- FreeVarMap.add v t st.s;
      TVar v
  with
    | Not_found -> TVar v (*raise (Failure 
			    (String.concat ""
			       ["reduction_aliase: the var is not an aliases ("; string_of_int v; ")"]
			    )
			 )*)
      
and reduction_destructor (st: typechecker_state) (s: interp_state) (te: term) (ldes: (term option) array) : term option = 
  match normalize te with
    | TApp (TConstr (i, _), l) -> (
	try
	  match ldes.(i) with
	    | None -> raise (ReductionCannotBePerformed "Catastrophic: No valid destructor case")
	    | Some te -> Some (TApp (te, l))
	with
	  | not_found -> raise (ReductionCannotBePerformed "Catastrophic: No destructor case")
      )
    | _ -> None

and reduction_loop (st: typechecker_state) (s: interp_state) (t: term) : term = 
(*
  let t = apply_substitution_term t s in
*)
  match t with
    | TType a -> TType a
    | TVar v -> if v >= 0 then TVar v else reduction_aliase st s v	
    | TPrim p -> TPrim p
    | TConstr (i, t) -> TConstr (i, t)
    | TCste c ->
	if not s.delta then TCste c else (
	  
	  match finddef c st.def with
	    | None -> raise (Failure (
			       String.concat " " (("no such definition:")::c::[])
			     )
			    )
	    | Some (n , (te, ty, DataDef)) -> if s.deltastrong then te else TCste c
	    | Some (n , (te, ty, TypeDef)) -> if s.deltastrong then te else TCste c
	    | Some (n , (te, ty, _)) -> (

		if s.deltaiotaweak then (
		  
		  try 
		    reduction_loop st s (extract te)
		  with
		    | DeltaIotaException -> TCste c
			
			
		) else (
		  
		  reduction_loop st s te
		    
		)
	      )

	)
	
    (* first intersting case: the let*)
    | TLet ((n, t1, ty), t2) ->
	(* depending on zeta we expand or not *)
	if (not s.zeta) then (
	  (* no expansion, are we lazy or eager ? *)
	  let t1 = if (s.strat = Eager ) then reduction_loop st s t1 else t1 in
	    tcst_pushqv st n t1 Explicite;
	    let t2 = reduction_loop st s t2 in
	    let ((_, te, _), t2) = tcst_popqv st t2 in
	      TLet ((n, te, ty), t2)      

	) else (

	  if s.strat = Eager then (

	    let t1 = reduction_loop st s t1 in
	    let s' = FreeVarMap.add 0 (shift_var t1 1) FreeVarMap.empty in
	    let t2 = apply_substitution_term t2 s' in
	    let t2 = (shift_var t2 (-1)) in
	      reduction_loop st s t2
	    
	  ) else (

	    let c = tcst_pushfv st "@" (TType Zero) in
	      st.s <- addsubstitution c t1 st.s;
	      let s' = FreeVarMap.add 0 (TVar c) FreeVarMap.empty in
	      let t2 = apply_substitution_term t2 s' in
	      let t2 = (shift_var t2 (-1)) in
		reduction_loop st s t2

	  )

	)

    | TLambda ((x, ty, n), te) -> (
	
	if s.betastrong then (

	  tcst_pushqv st x ty n;
	  let te = reduction_loop st s te in
	  let ((x, ty, n), te) = tcst_popqv st te in
	    TLambda ((x, ty, n), te)          

	) else (

	  TLambda ((x, ty, n), te)

	)

      )

    | TForall ((x, ty, n), te) -> (
	
	if s.betastrong then (

	  tcst_pushqv st x ty n;
	  let te = reduction_loop st s te in
	  let ((x, ty, n), te) = tcst_popqv st te in
	    TForall ((x, ty, n), te)          

	) else (

	  TForall ((x, ty, n), te)

	)

      )

    | TPhi (x, args, ty, tp, body) -> TPhi (x, args, ty, tp, body)

    | TInd (x, args, ty, lcons) -> TInd (x, args, ty, lcons)

    | TMatch (t, ldes, ty) -> (

	if not s.iota then TMatch (t, ldes, ty) else (

	  let t = reduction_loop st s t in

	  match reduction_destructor st s t ldes with
	    | None -> 
		if s.deltaiotaweak then
		  raise DeltaIotaException
		else
		  TMatch (t, ldes, ty)
	    | Some rhs -> reduction_loop st s rhs

	)

      )

    | TApp (hd, []) -> reduction_loop st s hd

    | TApp (hd, l) -> (

	match reduction_loop st s hd with
	  | TLambda ((x, ty, n), te) ->
	      if s.beta then (
		let arg = fst (List.hd l) in
		let tl = List.tl l in

		  if s.strat = Eager then (

		    let arg = reduction_loop st s arg in
		    let s' = FreeVarMap.add 0 (shift_var arg 1) FreeVarMap.empty in
		    let te = apply_substitution_term te s' in
		    let te = (shift_var te (-1)) in
		      reduction_loop st s (TApp (te, tl))

		  ) else (

		    let c = tcst_pushfv st "@" (TType Zero) in
		      st.s <- addsubstitution c arg st.s;
		      let s' = FreeVarMap.add 0 (TVar c) FreeVarMap.empty in
		      let te = apply_substitution_term te s' in
		      let te = (shift_var te (-1)) in
			reduction_loop st s (TApp (te, tl))
		  )
		  

	      ) else (
		
		TApp (reduction_loop st s hd, l)

	      )

	  | TPhi (x, args, ty, terminaison, body) -> (

	      if s.beta then (

		let s' = FreeVarMap.add 0 (shift_var (TPhi (x, args, ty, terminaison, body)) 1) FreeVarMap.empty in
		let body = apply_substitution_term body s' in
		let body = (shift_var body (-1)) in
		let te = List.fold_right (
		  fun hd acc ->
		    TLambda (hd, acc)
		) args body in
		  reduction_loop st s (TApp (te, l))

	      ) else (
		
		TApp (reduction_loop st s hd, l)

	      )

	    )

	  | TCste c -> (
	      
	      if not s.delta then (

		TApp (TCste c, l)

	      ) else (
		
		match finddef c st.def with
		  | None -> raise (Failure (
				     String.concat " " (("no such definition:")::c::[])
				   )
				  )
		  | Some (n , (te, ty, DataDef)) -> 
		      if s.strat = Eager then (

			TApp (TCste c, (List.map (fun (x, y) -> (reduction_loop st s x, y)) l))

		      ) else (

			TApp (TCste c, l)

		      )

		  | Some (n , (te, ty, TypeDef)) -> 
		      if s.strat = Eager then (
			
			TApp (TCste c, (List.map (fun (x, y) -> (reduction_loop st s x, y)) l))
			  
		      ) else (
			
			TApp (TCste c, l)
			  
		      )

		  | Some (n , (te, ty, _)) -> (
		     
		      match te with
			| TCste c' -> (

			    try 
			      reduction_loop st s (TApp (TCste c',l))
			    with
			      | DeltaIotaException -> TApp (hd, l)

			  )

			| TPhi (x, args, ty, terminaison, body) -> (

			    let s' = FreeVarMap.add 0 (TCste c) FreeVarMap.empty in
			    let body = apply_substitution_term body s' in
			    let body = (shift_var body (-1)) in
			      
			    let te = List.fold_right (
			      fun hd acc ->
				TLambda (hd, acc)
			    ) args body in

			      try 
				reduction_loop st s (TApp (te, l))
			      with
				| DeltaIotaException ->  TApp (hd, l)

			  )


			| _ -> (

			    try 				
			      reduction_loop st s (TApp (te, l))
			    with
			      | DeltaIotaException ->  TApp (hd, l)

			  )
 
		    )
		     
		   
	      )    
	      

	    )
	  | te -> TApp (te, l)

      )
	
    | te -> raise (ReductionCaseNotSupported te)
;;
