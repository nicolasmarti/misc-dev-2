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

  Copyright (C) Nicolas Marti
*)

open Ast;;
open Term;;
open Definition;;
open Varset;;
open Freshness;;
open Varset;;
open Varmap;;
open Printf;;
open Listext;;

type strategy = 
  | Lazy 
  | Eager;;

type interp_state = {
  strat: strategy;
  beta: bool;
  betastrong: bool;
  delta: bool;
  iota: bool;
  deltaiotaweak: bool;
  zeta: bool;
  eta: bool;
  mdef:  (term * term * defnature) objdef;
  mutable ctxt: (name * term * nature) list;
  mutable aliasesi: int;
  mutable aliases: term FreeVarMap.t ;
};;

let push_ctxt (st: interp_state) (d: (name * term * nature)) : unit =
  st.ctxt <- d::st.ctxt;
  st.aliases <- FreeVarMap.map (
    fun v ->      
      shift_var v 1
  ) st.aliases
;;

let pop_ctxt (st: interp_state) (t: term) : ((name * term * nature) * term) =
  let (good, bad) = FreeVarMap.fold (
    fun k v acc ->
      try 
	(
	  FreeVarMap.add
	    k
	    (shift_var v (-1))
	    (fst acc)
	, snd acc)
      with
	| MshiftException ->
	    (fst acc, (k, v)::(snd acc))
	    
  ) st.aliases (FreeVarMap.empty, []) in
    st.aliases <- good;
    let s = compose_substitution (List.rev bad) in
    let t = apply_substitution_term t s in
      match st.ctxt with
	| [] -> raise (Failure "pop_ctxt")
	| hd::tl -> 
	    st.ctxt <- tl;
	    (hd, t)
;;
    

exception ReductionCaseNotSupported of term;;
exception DeltaIotaException;;

let rec reduction (st: interp_state) (t: term) : term = 
  
  let t = 
    try 
      reduction_loop st t 
    with
      | DeltaIotaException -> t
      | ReductionCaseNotSupported te -> printf "cannot exec:\n"; pprintterm te false; raise (ReductionCaseNotSupported te)
  in
  let s = compose_substitution (List.rev (FreeVarMap.fold (
					    fun k v acc ->
					      (k,v)::acc
					  ) st.aliases []
					 )
			       ) in
  let t = apply_substitution_term t s in
    t    
and reduction_aliase (st: interp_state) (v: int) : term = 
  try 
    let t = FreeVarMap.find v st.aliases in
    let t = reduction_loop st t in
      st.aliases <- FreeVarMap.add v t st.aliases;
      Var v
  with
    | Not_found -> raise (Failure 
			    (String.concat ""
			       ["reduction_aliase: the var is not an aliases ("; string_of_int v; ")"]
			    )
			 )
      
and reduction_destructor (st: interp_state) (te: term) (ldes: (term * term) list) : term option = 
  (* to REDO !!!! *)
  List.fold_left (
    fun acc hd ->
      match acc with
	| Some te -> Some te
	| None ->
	    (* find better *)
	    match unification (fst hd) te st.mdef with
	      | Mgu (s, _) -> Some (apply_substitution_term (snd hd) s)
	      | _ -> None
  ) None ldes
and reduction_loop (st: interp_state) (t: term) : term = 
  (*
  pprintterm t false;
  printf "\n\n";
  *)
  let s = compose_substitution (List.rev (FreeVarMap.fold (
					    fun k v acc ->
					      (k,v)::acc
					  ) st.aliases []
					 )
			       ) in
  let t = apply_substitution_term t s in
  match t with
    | Type a -> Type a
    | Var v -> if v >= 0 then Var v else reduction_aliase st v	
    | Obj o -> Obj o
    | Constr (i, t) -> Constr (i, t)
    | Cste c ->
	if not st.delta then Cste c else (
	  
	  match finddef c st.mdef with
	    | None -> raise (Failure (
			       String.concat " " (("no such definition:")::c::[])
			     )
			    )
	    | Some (n , (te, ty, DataDef)) -> Cste c
	    | Some (n , (te, ty, TypeDef)) -> Cste c
	    | Some (n , (te, ty, _)) -> (

		if st.deltaiotaweak then (
		  
		  try 
		    reduction_loop st (extract te)
		  with
		    | DeltaIotaException -> Cste c
			
			
		) else (
		  
		  reduction_loop st te
		    
		)
	      )

	)
	
    (* first intersting case: the let*)
    | Let (n, t1, t2) ->
	(* depending on zeta we expand or not *)
	if (not st.zeta) then (
	  (* no expansion, are we lazy or eager ? *)
	  let t1 = if (st.strat = Eager ) then reduction_loop st t1 else t1 in
	    push_ctxt st (n, t1, Explicite);
	    let t2 = reduction_loop st t2 in
	    let ((_, te, _), t2) = pop_ctxt st t2 in
	      Let (n, te, t2)      

	) else (

	  if st.strat = Eager then (

	    let t1 = reduction_loop st t1 in
	    let s = (0, shift_var t1 1)::[] in
	    let t2 = apply_substitution_term t2 s in
	    let t2 = (shift_var t2 (-1)) in
	      reduction_loop st t2
	    
	  ) else (

	    let c = st.aliasesi in
	      st.aliasesi <- st.aliasesi - 1;
	      st.aliases <- FreeVarMap.add c t1 st.aliases;
	      let s = (0, shift_var (Var c) 1)::[] in
	      let t2 = apply_substitution_term t2 s in
	      let t2 = (shift_var t2 (-1)) in
		reduction_loop st t2

	  )

	)

    | Lambda ((x, ty, n), te) -> (
	
	if st.betastrong then (

	  push_ctxt st (x, ty, n);
	  let te = reduction_loop st te in
	  let ((x, ty, n), te) = pop_ctxt st te in
	    Lambda ((x, ty, n), te)          

	) else (

	  Lambda ((x, ty, n), te)

	)

      )

    | Forall ((x, ty, n), te) -> (
	
	if st.betastrong then (

	  push_ctxt st (x, ty, n);
	  let te = reduction_loop st te in
	  let ((x, ty, n), te) = pop_ctxt st te in
	    Lambda ((x, ty, n), te)          

	) else (

	  Forall ((x, ty, n), te)

	)

      )

    | Phi (x, args, ty, tp, body) -> Phi (x, args, ty, tp, body)

    | Ind (x, args, ty, lcons) -> Ind (x, args, ty, lcons)

    | Match (t, ldes, ty) -> (

	if not st.iota then Match (t, ldes, ty) else (

	  let t = reduction_loop st t in

	  match reduction_destructor st t ldes with
	    | None -> 
		if st.deltaiotaweak then
		  raise DeltaIotaException
		else
		  Match (t, ldes, ty)
	    | Some rhs -> reduction_loop st rhs

	)

      )

    | App ((hd, _)::[]) -> reduction_loop st hd

    | App ((App l, _)::l') -> App (l @ l')

    | App ((hd, b)::tl) -> (

	match hd with
	  | Lambda ((x, ty, n), te) ->
	      if st.beta then (
		let arg = fst (List.hd tl) in
		let tl = List.tl tl in

		  if st.strat = Eager then (

		    let arg = reduction_loop st arg in
		    let s = (0, shift_var arg 1)::[] in
		    let te = apply_substitution_term te s in
		    let te = (shift_var te (-1)) in
		      reduction_loop st (App ((te,b)::tl))

		  ) else (

		    let c = st.aliasesi in
		      st.aliasesi <- st.aliasesi - 1;
		      st.aliases <- FreeVarMap.add c arg st.aliases;
		      let s = (0, shift_var (Var c) 1)::[] in
		      let te = apply_substitution_term te s in
		      let te = (shift_var te (-1)) in
			reduction_loop st (App ((te,b)::tl))
		  )
		  

	      ) else (
		
		App ((reduction_loop st hd, b)::tl)

	      )

	  | Phi (x, args, ty, terminaison, body) -> (

	      if st.beta then (

		let s = (0, shift_var (Phi (x, args, ty, terminaison, body)) 1)::[] in
		let body = apply_substitution_term body s in
		let body = (shift_var body (-1)) in
		let te = List.fold_right (
		  fun hd acc ->
		    Lambda (hd, acc)
		) args body in
		  reduction_loop st (App ((te,b)::tl))

	      ) else (
		
		App ((reduction_loop st hd, b)::tl)

	      )

	    )

	  | Cste c -> (
	      
	      if not st.delta then (

		App ((Cste c, b)::tl)

	      ) else (
		
		match finddef c st.mdef with
		  | None -> raise (Failure (
				     String.concat " " (("no such definition:")::c::[])
				   )
				  )
		  | Some (n , (te, ty, DataDef)) -> 
		      if st.strat = Eager then (

			App ((Cste c, b)::(List.map (fun (x, y) -> (reduction_loop st x, y)) tl))

		      ) else (

			App ((Cste c, b)::tl)

		      )

		  | Some (n , (te, ty, TypeDef)) -> 
		      if st.strat = Eager then (
			
			App ((Cste c, b)::(List.map (fun (x, y) -> (reduction_loop st x, y)) tl))
			  
		      ) else (
			
			App ((Cste c, b)::tl)
			  
		      )

		  | Some (n , (te, ty, _)) -> (
		     
		      match te with
			| Cste c' -> (

			    try 
			      reduction_loop st (App ((Cste c',b)::tl))
			    with
			      | DeltaIotaException -> App ((hd, b)::tl)

			  )

			| Phi (x, args, ty, terminaison, body) -> (

			    let s = (0, Cste c)::[] in
			    let body = apply_substitution_term body s in
			    let body = (shift_var body (-1)) in
			      
			    let te = List.fold_right (
			      fun hd acc ->
				Lambda (hd, acc)
			    ) args body in

			      try 
				reduction_loop st (App ((te,b)::tl))
			      with
				| DeltaIotaException ->  App ((hd, b)::tl)

			  )


			| _ -> (

			    try 				
			      reduction_loop st (App ((te,b)::tl))
			    with
			      | DeltaIotaException ->  App ((hd, b)::tl)

			  )
 
		    )
		      
	      )
		
	      

	    )

      )
	
    | te -> raise (ReductionCaseNotSupported te)
;;

