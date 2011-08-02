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
open Universe;;
open Printf;;
open Varmap;;
open Astparser;;
open Pparser;;
open Pprinter;;
open Listext;;

type typechecker_state = {
  (* quantified variable, term at the level of previous quantification 
     debruijn indice

     (0)::(1)::...::(n)::[]

  *)
  mutable qv : (name * term * nature) list;

  (* free variable, term at the current level of quantification 
     negative reverse debruijn indice, plus a term that correspond to the 
     sum of substitution on the fv

     (-n)::...::(-2)::(-1)::[]
  *)
  mutable fv: (name * term option * term option) list;
  mutable univ_var: VarSet.t;
  mutable univ_constraint: univ_level_constraint list;
  mutable term_storage: (term list) list;
  mutable def: (term * term * defnature) objdef;
  oracles: (typechecker_state -> term -> term option) list;
  coercion: ((term * term) * term) list;
  mutable tc_tree: token list list;
};;

let st_stat (st: typechecker_state) =
  (List.length st.qv,
   List.map List.length st.term_storage   
  )
;;


let tcst_applysubst (st: typechecker_state) (s: substitution) : unit =
  st.qv <- snd (List.fold_left (
		  fun (s', l') (x, te, n) ->
		    let s'' = shift_var_substitution_err s' (-1) in
		    let te' = apply_substitution_term te s' in
		      (s'', l' @ (x, te', n)::[])			
		) (s, []) st.qv
	       );
  st.fv <-  List.map (fun (hd1, hd2, hd3) -> 
			(hd1,
			 (match hd2 with
			    | None -> None
			    | Some hd2 -> Some (apply_substitution_term hd2 s)
			 ),
			 (match hd3 with
			    | None -> None
			    | Some hd3 -> Some (apply_substitution_term hd3 s)
			 )  
			)
			 
		      ) st.fv;
  st.term_storage <- snd (List.fold_left (
			 fun (s', l') lt ->
			   let lt' = apply_substitution_listterm lt s' in
			   let s'' = shift_var_substitution_err s' (-1) in
			     (s'', l' @ lt'::[])			
			  ) (s, []) st.term_storage
			 )    
;;

let tcst_pushterm (st: typechecker_state) (t: term) : unit =
  (*printf "push\n"; flush stdout;*)
  if (List.length st.term_storage = 0) then (

    st.term_storage <- (t::[])::[]

  ) else (

    st.term_storage <- (t::(List.hd st.term_storage)) :: (List.tl st.term_storage)

  )
;;

let tcst_pushterm2 (st: typechecker_state) (t: term) : (int * int) =
  (*printf "push\n"; flush stdout;*)
  if (List.length st.term_storage = 0) then (

    st.term_storage <- (t::[])::[]

  ) else (

    st.term_storage <- (t::(List.hd st.term_storage)) :: (List.tl st.term_storage)

  );
  let i1 = List.length st.term_storage in
  let i2 = List.length (List.hd st.term_storage) in
    (i1, i2)
;;


let tcst_popterm (st: typechecker_state) : term =
  (*printf "pop\n"; flush stdout;*)
  let te = List.hd (List.hd st.term_storage) in
    st.term_storage <- (List.tl (List.hd st.term_storage)) :: (List.tl st.term_storage);
    te
;;

let tcst_getterm (st: typechecker_state) (c: int * int) : term =
  try (
    let l1 = List.length st.term_storage in
    let l = (List.nth st.term_storage (l1 - fst c)) in
    let l2 = List.length l in
      (shift_var (List.nth l (l2 - snd c)) (l1 - fst c))
  ) with
    | e -> (*printf "tcst_getterm:";*) raise e
;;

let tcst_qvtype (st: typechecker_state) (v: int) : term =
  try (
    if (v < 0 || v >= List.length st.qv) then
      raise (Failure "No such qv")
    else
      let t = (fun (_, te, _) -> te) (List.nth st.qv v) in
	shift_var t (v + 1)    
  ) with
    | e -> (*printf "tcst_qvtype:";*) raise e
;;

let tcst_fvtype (st: typechecker_state) (v: int) : term =
  try (
    match List.nth st.fv (List.length st.fv + v) with
      | (_, None, _) -> raise (Failure "fv is no more active")
      | (_, Some te, _) -> te
  ) with
    | e -> (*printf "tcst_fvtype:";*) raise e
;;

let tcst_fvvalue (st: typechecker_state) (v: int) : term =
  try (
    match List.nth st.fv (List.length st.fv + v) with
      | (_, Some _, Some v) -> v
      | _ -> raise (Failure "fv is no more active")
  ) with
    | e -> (*printf "tcst_fvtype:";*) raise e
;;

let tcst_fvname (st: typechecker_state) (v: int) : name =
  try (
    match List.nth st.fv (List.length st.fv + v) with
      | (n, _, _) -> n
  ) with
    | e -> (*printf "tcst_fvname:";*) raise e
;;

let tcst_vartype (st: typechecker_state) (v: int) : term =
  if (v < 0) then
    tcst_fvtype st v
  else
    tcst_qvtype st v
;;

let tcst_pushqv (st: typechecker_state) (x: string) (ty: term) (n: nature) : unit =
  st.qv <- (x, ty, n)::st.qv;
  st.fv <- List.map (fun (hd1, hd2, hd3) -> 
		       (hd1,
			(match hd2 with
			  | None -> None
			  | Some hd2 -> Some (shift_var hd2 1)
			),
			(match hd3 with
			   | None -> None
			   | Some hd3 -> Some (shift_var hd3 1)
			)
		       )
		    ) st.fv;
  st.term_storage <- ([])::st.term_storage
;;

let tcst_popqv (st: typechecker_state) : (string * term * nature) =
  let res = List.hd st.qv in
    st.fv <- List.map (fun (hd1, hd2, hd3) -> 
			 (hd1,
			  (match hd2 with
			     | None -> None
			     | Some hd2 -> 
				 try 
				   Some (shift_var hd2 (-1))
				 with
				   | MshiftException -> (
				       None
				     )				       
			  ),
			  (match hd3 with
			     | None -> None
			     | Some hd3 -> 
				 try 
				   Some (shift_var hd3 (-1))
				 with
				   | MshiftException -> (
				       None
				     )				       
			  )
			 )
		      ) st.fv;
    st.qv <- List.tl st.qv;
    st.term_storage <- List.tl st.term_storage;
    res
;;

let tcst_pushfv (st: typechecker_state) (n: name) (ty: term) : int =
  st.fv <- (n, Some ty, Some (Var (- (List.length st.fv + 1))))::st.fv;
  (- (List.length st.fv))
;;


let tcst_addconstraint (st: typechecker_state) (uc: univ_level_constraint list) =
  st.univ_var <- List.fold_left (fun acc hd ->
				   acc +++ (ulc_var hd)
				) st.univ_var uc;
  st.univ_constraint <- st.univ_constraint @ uc
;;

(* Debug material *)

let tcst_pushtoken (st: typechecker_state) (t: token) : unit =
  if (List.length st.tc_tree = 0) then (

    st.tc_tree <- (t::[])::[]

  ) else (

    st.tc_tree <- (t::(List.hd st.tc_tree)) :: (List.tl st.tc_tree)

  )
;;

let tcst_pushtokenlevel (st: typechecker_state) : unit =  
  st.tc_tree <- ([])::st.tc_tree
;;


let tcst_poptokenlevel (st: typechecker_state) : unit = 
  let hd = (List.hd st.tc_tree) in
  let tlhdhd = List.hd (List.hd (List.tl st.tc_tree)) in
  let tlhdtl = List.tl (List.hd (List.tl st.tc_tree)) in
  let tltl = (List.tl (List.tl st.tc_tree)) in
    st.tc_tree <-((Frac (tlhdhd, List.rev hd))::tlhdtl)::tltl
;;

let tcst_pushtokens (st: typechecker_state) (ts: token list) : unit =
  let hd = (List.hd st.tc_tree) in
  let tlhdhd = List.hd (List.hd (List.tl st.tc_tree)) in
  let tlhdtl = List.tl (List.hd (List.tl st.tc_tree)) in
  let tltl = (List.tl (List.tl st.tc_tree)) in
    match tlhdhd with
      | Box l -> st.tc_tree <- hd :: (Box (l @ Newline :: ts) :: tlhdtl) :: tltl
      | _ -> ()	  
;;


(**)

exception TermCheckFailure of string;;

type astOrterm =
  | Left of ast
  | Right of term
;;

let termcheckgoal2token (te: astOrterm) (ty: term option) (st: typechecker_state) =
  Box (
    (intercalate (Verbatim ",") (snd (
				    List.fold_left (
				      fun acc hd ->
					(hd :: (fst acc), 
					 Box ((snd acc) @ (Verbatim "(") :: (Verbatim ((fun (n, _, _) -> n) hd)) :: (Verbatim ":") :: (Space 1) :: (let t = term2token ((fun (_, ty, _) -> ty) hd) false (List.map (fun (n, _, _) -> n) (fst acc)) in Box t) :: (Verbatim ")") :: []) :: []
					)
				    ) ([], []) (List.rev st.qv)
				  )
				 )
    ) @
    (Verbatim "|-") :: (Space 1) ::
      (match te with
	 | Left te -> (
	     match pparser_pprinter astpparser te with
	       | None -> (Verbatim "???")
	       | Some t -> t
	   )
	 | Right te -> (
	       let t = term2token te false (
		 List.map (fun (n, _, _) -> n) st.qv
	       ) in
		 Box t
	   )
      )
    :: (Space 1) :: (Verbatim ":") :: (Space 1) :: (match ty with
						      | None -> (Verbatim "???")
						      | Some te -> let t = term2token te false (
							  List.map (fun (n, _, _) -> n) st.qv
							) in Box t) :: []
  )
;;

let termcheckterm2token (te: term) (st: typechecker_state) =
  Box (
    (intercalate (Verbatim ",") (snd (
				    List.fold_left (
				      fun acc hd ->
					(hd :: (fst acc), 
					 Box ((snd acc) @ (Verbatim "(") :: (Verbatim ((fun (n, _, _) -> n) hd)) :: (Verbatim ":") :: (Space 1) :: (let t = term2token ((fun (_, ty, _) -> ty) hd) false (List.map (fun (n, _, _) -> n) (fst acc)) in Box t) :: (Verbatim ")") :: []) :: []
					)
				    ) ([], []) (List.rev st.qv)
				  )
				 )
    ) @
    (Verbatim "|-") :: (Space 1) ::
      (let t = term2token te false (
	 List.map (fun (n, _, _) -> n) st.qv
       ) in
	 Box t
      )     
    :: []
  )
;;


let termcheckres2token (te: term) (ty: term) (st: typechecker_state) =
 let fv = FreeVarSet.elements (fv te) in
    
  Box (
    (*
    (intercalate (Verbatim ",") (
       List.map (
	 fun hd ->
	   Box (
	     (Verbatim "(") ::
	       (Verbatim (string_of_int hd)) ::
	       (Verbatim ", ") ::
	       (try 
		  Verbatim (tcst_fvname st hd)
		with
		  | _ -> (Verbatim "????")
	       ) ::
	       (Verbatim ", ") ::
	       (try 
		  let t = term2token (tcst_fvtype st hd) false (
		    List.map (fun (n, _, _) -> n) st.qv
		  ) in
		    Box t
		with
		  | _ -> (Verbatim "None")
	       ) ::
	       (Verbatim ", ") ::
	       (try
		  let t = term2token (tcst_fvvalue st hd) false (
		    List.map (fun (n, _, _) -> n) st.qv
		  ) in
		    Box t
		with
		  | _ -> (Verbatim "None")
	       ) ::
	       (Verbatim ")") :: []
	   )
       ) (List.map (fun x -> (-x)) (iota 1 20))
     )) @ Newline :: 
*)
    (intercalate (Verbatim ",") (snd (
				    List.fold_left (
				      fun acc hd ->
					(hd :: (fst acc), 
					 Box ((snd acc) @ (Verbatim "(") :: (Verbatim ((fun (n, _, _) -> n) hd)) :: (Verbatim ":") :: (Space 1) :: (let t = term2token ((fun (_, ty, _) -> ty) hd) false (List.map (fun (n, _, _) -> n) (fst acc)) in Box t) :: (Verbatim ")") :: []) :: []
					)
				    ) ([], []) (List.rev st.qv)
				  )
				 )
    ) @
    (Verbatim "|-") :: (Space 1) ::
      (let t = term2token te false (
	 List.map (fun (n, _, _) -> n) st.qv
       ) in
	 Box t
      )
    :: (Space 1) :: (Verbatim ":") :: (Space 1) :: (let t = term2token ty false (
						      List.map (fun (n, _, _) -> n) st.qv
						    ) in Box t) :: []
      )
;;


let rec termcheck
    (st: typechecker_state)
    (te: astOrterm)
    (ty: term option)
    :
    (term * term) =
  tcst_pushtoken st (termcheckgoal2token te ty st);
  tcst_pushtokenlevel st;
  let prest = st_stat st in
  let (te', inferedty, nty) = (
    (* under here we only infer *)
    match te with

      (* Type *)
      | (Left Ast.Type) -> (
	  let univ_fn = (fresh_name_list_name st.univ_var "univ") in
	    st.univ_var <- univ_fn ++ st.univ_var;
	    let type_ty = Succ (Level univ_fn) in
	      (Type (Level univ_fn), Type type_ty, None)
	)
      | Right (Type univ_fn) -> (
	  let type_ty = Succ univ_fn in
	    (Type univ_fn, Type type_ty, None)
	)

      (* Forall *)
      | Left (Ast.Forall (n, x, ty, te)) -> (
	  let univ_fn = (fresh_name_list_name st.univ_var "univ") in
	    st.univ_var <- univ_fn ++ st.univ_var;
	    match termcheck st (Left ty) (Some (Type (Level univ_fn))) with
	      | (ty, Type alpha) -> (
		  tcst_pushqv st x ty n;
		  let univ_fn = (fresh_name_list_name st.univ_var "univ") in
		    st.univ_var <- univ_fn ++ st.univ_var;		
		    match termcheck st (Left te) (Some (Type (Level univ_fn))) with
		      | (te, Type beta) -> (
			  let (x, ty, n) = tcst_popqv st in
			    (Forall ((x, ty, n), te), Type (Max (alpha::beta::[])), None)
			)
		      | _ -> raise (TermCheckFailure "termcheck Forall (2): Does not have type Type")
		)
	      | _ -> raise (TermCheckFailure "termcheck Forall (1): Does not have type Type")
	)
      | Right (Forall ((x, ty, n), te)) -> (
	  let univ_fn = (fresh_name_list_name st.univ_var "univ") in
	    st.univ_var <- univ_fn ++ st.univ_var;
	    match termcheck st (Right ty) (Some (Type (Level univ_fn))) with
	      | (ty, Type alpha) -> (
		  tcst_pushqv st x ty n;
		  let univ_fn = (fresh_name_list_name st.univ_var "univ") in
		    st.univ_var <- univ_fn ++ st.univ_var;				    
		    match termcheck st (Right te) (Some (Type (Level univ_fn))) with
		      | (te, Type beta) -> (
			  let (x, ty, n) = tcst_popqv st in
			    (Forall ((x, ty, n), te), Type (Max (alpha::beta::[])), None)
			)
		      | _ -> raise (TermCheckFailure "termcheck Forall (2): Does not have type Type")
		)
	      | _ -> raise (TermCheckFailure "termcheck Forall (1): Does not have type Type")
	)
	  
      (* Lambda *)
      | Left (Ast.Lambda (n, x, lty, te)) ->(
	  
	  (*printf "Lambda L\n";*)
	  (* first termcheck te with x in the env *)
	  let (tyte, tyty) = termcheck st (Left lty) None in
	    (* we push x *)
	    tcst_pushqv st x tyte n;
	    (* we termcheck te *)

	    let nty2 = 
	      match ty with 
		| None -> None
		| Some ty -> 
		    match betared ty st.def with
		      | Forall ((x, ty, n), te) -> (
			  Some te
			)
		      | _ -> None
	    in


	    let (tete, tety) = termcheck st (Left te) nty2 in
	      (* we pull out x, te remains unchanged because it wil be quantified over x *)
	    let (x, ty, n) = tcst_popqv st in
	      (* we just need to be sure that the infered type of the lambda is correct *)
	    let (_, _) = termcheck st (Right (Forall ((x, ty, n), tety))) None in
	      ((Lambda ((x, ty, n), tete)), 
	       (Forall ((x, ty, n), tety)), 
	       (match nty2 with
		 | None -> None
		 | Some _ -> Some (Forall ((x, ty, n), tety))
	       )
	      )	   
	)

      | Right (Lambda ((x, lty, n), te)) ->(

	  (*printf "Lambda R\n";*)
	  (* first termcheck te with x in the env *)

	  (* NONE !!!!! *)
	  let (tyte, tyty) = termcheck st (Right lty) None in
	    (* we push x *)
	    tcst_pushqv st x tyte n;
	    (* we termcheck te *)

	    let nty2 = 
	      match ty with 
		| None -> None
		| Some ty -> 
		    match betared ty st.def with
		      | Forall ((x, ty, n), te) -> (
			  Some te
			)
		      | _ -> None
	    in


	    (* NONE !!!!! *)
	    let (tete, tety) = termcheck st (Right te) nty2 in
	      (* we pull out x, te remains unchanged because it wil be quantified over x *)
	    let (x, ty, n) = tcst_popqv st in
	      (* we just need to be sure that the infered type of the lambda is correct *)
	    let (_, _) = termcheck st (Right (Forall ((x, ty, n), tety))) None in
	      ((Lambda ((x, ty, n), tete)), 
	       (Forall ((x, ty, n), tety)), 	        
	       (match nty2 with
		 | None -> None
		 | Some _ -> Some (Forall ((x, ty, n), tety))
	       )
	      )	   
	)

      (* term Var *)

      | Right (Var v) -> (

	  try (
	    (Var v, tcst_vartype st v, None)	      
	  ) with
	    | Failure s ->
		raise (TermCheckFailure (
			 s
		       )
		      )

	)

      (* term Cste *)

      | Right (Cste c) -> (
	  match finddef c st.def with
	    | None -> raise (TermCheckFailure (
			       String.concat " " (("no such definition:")::c::[])
			     )
			    )
	    | Some (n , (te, ty, nature)) -> (Cste c, ty, None)
	)

      (* Ast Symb *) 
      | Left (Symb (_, x)) -> (

	  (* first lookup at qv *)
	  let qv = List.fold_left (
	    fun acc (hd, _, _) ->
	      match acc with
		| (_, Some _) -> acc
		| (i, None) ->
		    if (x = hd) then 
		      (i, Some i)
		    else
		      (i+1, None)
	  ) (0, None) st.qv in
	    match qv with
	      | (_, Some i) ->
		  (fun (hd1, hd2) -> (hd1, hd2, None)) (termcheck st (Right (Var i)) ty)
	      | _ -> 
		  (* then we look at fv *)
		  let fv = List.fold_left (
		    fun acc (hd, _, _) ->
		      match acc with
			| (_, Some _) -> acc
			| (i, None) ->
			    if (x = hd) then 
			      (i, Some i)
			    else
			      (i+1, None)
		  ) (-List.length st.fv, None) st.fv in
		    match fv with
		      | (_, Some i) ->
			  (fun (hd1, hd2) -> (hd1, hd2, None)) (termcheck st (Right (Var i)) ty)
		      | _ -> 
			  (* if yet nothing -> look for a cste *)
			  try
			    (fun (hd1, hd2) -> (hd1, hd2, None)) (termcheck st (Right (Cste x)) ty)
			  with
			    | TermCheckFailure s -> 
				(* definitely no trace of that symbol ... let register it as a fv *)
				let univ_fn = (fresh_name_list_name st.univ_var "univ") in
				  st.univ_var <- univ_fn ++ st.univ_var;
				  let m_tyty = Type (Level univ_fn) in
				  let m_ty = tcst_pushfv st "@new_symb_gen_ty@" m_tyty in
				  let mv = tcst_pushfv st x (Var m_ty) in
				    tcst_pushtokens st ((Verbatim "new symbol: ") :: (Verbatim x) :: (Verbatim "  ==> ") :: (Verbatim (string_of_int mv)) :: []);
				    (Var mv, Var m_ty, None)	      

				
			    
	)

      (* Let *)
      | Left (Ast.Let (x, te1, te2)) -> (

	  (* NONE !!!!! *)
	  let (te1, ty1) = termcheck st (Left te1) None in
	    tcst_pushterm st te1;
	    tcst_pushqv st x ty1 Explicite;
	    
	    let (te2, ty2) = termcheck st (Left te2) (match ty with
							| None -> None
							| Some ty -> Some (shift_var ty 1)
						     ) in
	    let (x, ty1, _) = tcst_popqv st in
	      let te1 = tcst_popterm st in
		(Let (x, te1, te2), shift_var ty2 (-1), None)

	)

      | Right (Let (x, te1, te2)) -> (

	  (* NONE !!!!! *)
	  let (te1, ty1) = termcheck st (Right te1) None in
	    tcst_pushterm st te1;
	    tcst_pushqv st x ty1 Explicite;

	    (* NONE !!!!! *)
	    let (te2, ty2) = termcheck st (Right te2) (match ty with
							| None -> None
							| Some ty -> Some (shift_var ty 1)
						     ) in
	    let (x, ty1, _) = tcst_popqv st in
	      let te1 = tcst_popterm st in
		(Let (x, te1, te2), shift_var ty2 (-1), None)

	)

      (* Avar *) 
      | Left (Ast.Avar) -> (

	  let oracle_res =

	    match ty with 
	      | None -> None
	      | Some ty ->

		  List.fold_left (
		    
		    fun acc hd ->
		      match hd st ty with
			| None -> acc
			| Some proof ->
			    
			    Some (termcheck st (Right proof) (Some ty))			  
			  
		  ) None st.oracles

	  in

	    match oracle_res with
	      | None ->

		  (* first build the type, itself as fv *)
		  let univ_fn = (fresh_name_list_name st.univ_var "univ") in
		    st.univ_var <- univ_fn ++ st.univ_var;
		    let m_tyty = Type (Level univ_fn) in
		    let m_ty = tcst_pushfv st "@left_avar_gen_ty@" m_tyty in
		    let mv = tcst_pushfv st "@left_avar_gen@" (Var m_ty) in
		      tcst_pushtokens st ((Verbatim "Avar ==> ") :: (Verbatim (string_of_int mv)) :: []);
		      (Var mv, Var m_ty, None)	      

	      | Some res -> (fun (hd1, hd2) -> (hd1, hd2, None)) res
	)

      (* AST App *) 
      (* here the code is a little bit different than the term one
	 this is because the implicite arguments are put here
      *)
      | Left (Ast.App l) -> (

	  let l = 
	    match flattenastapp (Ast.App l) with
	      | Ast.App l -> l
	      | _ -> raise (TermCheckFailure "Should never be there")
	  in
	    
	  match l with
	    | [] -> raise (TermCheckFailure "empty list of applications")
	    | hd::[] -> (fun (hd1, hd2) -> (hd1, hd2, None)) (termcheck st (Left hd) ty)
	    | hd::tl -> (

		(* NONE !!!!! *)
		let (fte, fty) = termcheck st (Left hd) None in
		  (*
		  printf "function:\n";
		  printf "term: "; pprintterm fte false;
		  printf "type: "; pprintterm fty false;
		  printf "\n";
		  *)

		  tcst_pushterm st fte;		  
		  tcst_pushterm st fty;
		  
		  let l = Listext.fold_left2 (
		    		    	  
		    fun l hd tl ->
		      
		      let fty = tcst_popterm st in

		      let (x, ty, n, te) = 
			(* that is  wrong *)
			match betared fty st.def with
			  | Forall ((x, ty, n), te) -> (
			      (x, ty, n, te)
			    )
			  | Cste n -> (
			      match finddef n st.def with
				| Some (_ , (Forall ((x, ty, n), te), tty, nature)) -> (
				    (x, ty, n, te)
				  )
				| _ -> raise (TermCheckFailure "termcheck: App of a non Forall type(1)")
			    )
			  | Var x -> (

			      if (x >= 0) then raise (TermCheckFailure "termcheck: App of a non Forall type(2)")
			      else

				let univ_fn1 = (fresh_name_list_name st.univ_var "univ") in
				  st.univ_var <- univ_fn1 ++ st.univ_var;
				  let m_tyty1 = Type (Level univ_fn1) in
				  let m_ty1 = tcst_pushfv st "@left_aapp_gen_ty1@" m_tyty1 in
				  let mv1 = tcst_pushfv st "@left_aapp_gen1@" (Var m_ty1) in
				    
				  let univ_fn2 = (fresh_name_list_name st.univ_var "univ") in
				    st.univ_var <- univ_fn2 ++ st.univ_var;
				    let m_tyty2 = Type (Level univ_fn2) in
				    let m_ty2 = tcst_pushfv st "@left_aapp_gen_ty2@" m_tyty2 in
				    let mv2 = tcst_pushfv st "@left_aapp_gen2@" (Var m_ty2) in
				      
				    let t = Forall (("@??@", Var mv1, Explicite), Var mv2) in 		      				      
				    let s = (x, t)::[] in
				      tcst_applysubst st s;
				      ("@??@", Var mv1, Explicite, Var mv2)

			    )
			  | t -> (
			      
			      printf "*******************\n";
			      pprintterm (betared fty st.def) false;
			      printf "*******************\n";
			      flush stdout;
			      
			      raise (TermCheckFailure "termcheck: App of a non Forall type(3)")
			    )
		      in
			
			if (n = Hidden) then (

			  tcst_pushterm st (Forall ((x, ty, Explicite), te));	  
			  (l, (Ast.Avar::hd::tl))
			      
			) else (
			  (*			  
			  printf "current type: "; pprintterm (Forall ((x, ty, Explicite), te)) false;
			  printf "\n";
			  *)
			  tcst_pushterm st (Forall ((x, ty, Explicite), te));
			  let (argte, argty) = termcheck st (Left hd) (Some ty) in
			    (*
			    printf "argument:\n";
			    printf "term: "; pprintterm argte false;
			    printf "type: "; pprintterm argty false;
			    printf "type annotation: "; pprintterm ty false;
			    printf "\n";
			    *)
			  let (Forall ((x, ty, Explicite), te)) = tcst_popterm st in
			  let s = (0, shift_var argte 1)::[] in
			  let inferedty = shift_var (apply_substitution_term (te) s) (-1) in
			    tcst_pushtokens st ((Verbatim "infered type: ") :: (let t = term2token inferedty false (List.map (fun (n, _, _) -> n) st.qv) in Box t) :: []);
			    tcst_pushterm st argte;
			    tcst_pushterm st inferedty;
			    
			    ((n = Implicite)::l, tl)			    
			      
			)
			  
		  ) ((false)::[]) tl in
		  let ty = tcst_popterm st in
		  let l = 
		    List.fold_right (
		      fun hd acc ->
			
			let te = tcst_popterm st in
			  (te, hd) :: acc

		    ) (List.rev l) [] in
		    (App l, ty, None)
	      )
	)

      (* term App *) 

      | Right (App l) -> (

	  match l with
	    | [] -> raise (TermCheckFailure "empty list of applications")
	    | (hd, n)::[] -> (fun (hd1, hd2) -> (hd1, hd2, None)) (termcheck st (Right hd) ty)
	    | (hd, n)::tl -> (

		(* NONE !!!!! *)
		let (fte, fty) = termcheck st (Right hd) None in

		  tcst_pushterm st fte;
		  tcst_pushterm st fty;
		  
		  let l = Listext.fold_left2 (
		    		    	  
		    fun l (hd, nat) tl ->
		      
		      let fty = tcst_popterm st in

		      let (x, ty, n, te) = 
			(* that is  wrong *)
			match betared fty st.def with
			  | Forall ((x, ty, n), te) -> (
			      (x, ty, n, te)
			    )
			  | Cste n -> (
			      match finddef n st.def with
				| Some (_ , (Forall ((x, ty, n), te), tty, nature)) -> (
				    (x, ty, n, te)
				  )
				| _ -> raise (TermCheckFailure "termcheck: App of a non Forall type")
			    )
			  | Var x -> (
			      if (x >= 0) then raise (TermCheckFailure "termcheck: App of a non Forall type")
			      else

				let univ_fn1 = (fresh_name_list_name st.univ_var "univ") in
				  st.univ_var <- univ_fn1 ++ st.univ_var;
				  let m_tyty1 = Type (Level univ_fn1) in
				  let m_ty1 = tcst_pushfv st "@right_app_gen_ty1@" m_tyty1 in
				  let mv1 = tcst_pushfv st "@right_app_gen1@"(Var m_ty1) in
				    
				  let univ_fn2 = (fresh_name_list_name st.univ_var "univ") in
				    st.univ_var <- univ_fn2 ++ st.univ_var;
				    let m_tyty2 = Type (Level univ_fn2) in
				    let m_ty2 = tcst_pushfv st "@right_app_gen_ty2@" m_tyty2 in
				    let mv2 = tcst_pushfv st "@right_app_gen2@" (Var m_ty2) in
				      
				    let t = Forall (("@??@", Var mv1, Explicite), Var mv2) in 		      				      
				    let s = (x, t)::[] in
				      tcst_applysubst st s;
				      ("@??@", Var mv1, Explicite, Var mv2)
			    )
			  | _ -> raise (TermCheckFailure "termcheck: App of a non Forall type")
		      in
			
			tcst_pushterm st (Forall ((x, ty, Explicite), te));
			let (argte, argty) = termcheck st (Right hd) (Some ty) in
			let (Forall ((x, ty, Explicite), te)) = tcst_popterm st in
			let s = (0, shift_var argte 1)::[] in
			let inferedty = shift_var (apply_substitution_term (te) s) (-1) in
			  tcst_pushtokens st ((Verbatim "infered type: ") :: (let t = term2token inferedty false (List.map (fun (n, _, _) -> n) st.qv) in Box t) :: []);
			  tcst_pushterm st argte;
			  tcst_pushterm st inferedty;
			  (nat::l, tl)			    
			    
			  
		  ) (n::[]) tl in
		  let ty = tcst_popterm st in
		  let l = 
		    List.fold_right (
		      fun hd acc ->
			
			let te = tcst_popterm st in
			  (te, hd) :: acc
			    
		    ) (List.rev l) [] in
		    (App l, ty, None)
	      )

	)

      (* term Obj *) 

      | Right (Obj o) -> (

	  (Obj o, o#get_type, None)

	)	  

      (* term Constr *) 

      | Right (Constr (i, t)) -> (

	  (* NONE !!!!! *)
	  let (tte, tty) = termcheck st (Right t) None in
	  let (largs, lcons) = 
	    (* that is wrong *)
	    match betared tte st.def with
	      | Ind (x, largs, ty, lcons) -> (
		  if (List.length lcons <= i) then
		    raise (TermCheckFailure "termcheck: Cste has no such destructor")
		  else
		    (largs, shift_var (apply_substitution_term (List.nth lcons i) ((0, t)::[])) (-1))
		)
	      | Cste n -> (
		  match finddef n st.def with
		    | Some (n , (Ind (x, largs, ty, lcons), tty, nature)) -> (
			if (List.length lcons <= i) then
			  raise (TermCheckFailure "termcheck: Cste has no such destructor")
			else
			  (largs, shift_var (apply_substitution_term (List.nth lcons i) ((0, t)::[])) (-1))
		      )
		    | _ -> raise (TermCheckFailure "termcheck: Cste of a non Inductive type")
		)
	      | _ -> raise (TermCheckFailure "termcheck: Cste of a non Inductive type")
	  in
	  let ty = 
	    List.fold_right (
	      fun hd acc ->
		Forall (hd, acc)
	    ) largs lcons in
	    (Constr (i, tte), ty, None)	  

	)	  

      (* AST Constr *) 

      | Left (Ast.Constr (i, t)) -> (

	  let (tte, tty) = termcheck st (Left t) None in
	  let (te, ty) = termcheck st (Right (Constr (i, tte))) ty in
	    (te, ty, None)
	    
	)

      (* term Ind *) 

      | Right (Ind (x, largs, ty, lcons)) -> (


	  (* directly return the type V largs . ty ??? *)
	  let (_, xty) = List.fold_right (
	    fun (x, ty, n) (i, te) ->
	      (i + 1, Forall ((x, ty, n), te))		  
	  ) largs (0, ty) in		
	    (Ind (x, largs, ty, lcons), xty, None)	    
	    (*raise (TermCheckFailure "termcheck: Not Yet Implemented")*)

	)	  

      | Left (Ast.Ind (x, largs, ty, lcons)) -> (

	  (* first we termcheck/input the arguments *)
	  List.fold_left (
	    fun acc (n, x, te) ->
	      let univ_fn = (fresh_name_list_name st.univ_var "univ") in
		st.univ_var <- univ_fn ++ st.univ_var;
		let (tete, tety) = termcheck st (Left te) (Some (Type (Level univ_fn))) in
		  tcst_pushqv st x tete n	    
	  ) () largs;

	  (* then we typecheck ty, and finally push x as forall args . ty *)
	  let univ_fn = (fresh_name_list_name st.univ_var "univ") in
	    st.univ_var <- univ_fn ++ st.univ_var;
	    let (tyte, tyty) = termcheck st (Left ty) (Some (Type (Level univ_fn))) in	      
	      tcst_pushterm st tyte;
	      let (_, xty) = List.fold_right (
		fun (n, x, _) (i, te) ->
		  (i + 1, Forall ((x, shift_var' ((fun (_, x, _) -> x) (List.nth st.qv i)) (i + 1) (List.length largs), n), te))		  
	      ) largs (0, shift_var' tyte (List.length largs) (List.length largs)) in		
		tcst_pushqv st x xty Explicite;		
	      
	      (* finally we typecheck all the constructors *)
	      List.fold_right (
		fun (hd1, hd2) acc ->
		  let univ_fn = (fresh_name_list_name st.univ_var "univ") in
		    st.univ_var <- univ_fn ++ st.univ_var;
		    let (hdte, hdty) = termcheck st (Left hd2) (Some (Type (Level univ_fn))) in
		      tcst_pushterm st hdte
	      ) lcons ();

	      (* TODO: verify the wf of the constructor (conclusion is a positive occurence of x, only (at least) semi positive occurence of x in hyp) *)

	      (* we build the term *)
	      let lcons' = List.fold_right (
		fun _ acc ->
		  let te = tcst_popterm st in
		    te :: acc
	      ) lcons [] in

	      let _ = tcst_popqv st in
		
	      let ty' = tcst_popterm st in

	      let largs' = List.fold_right (
		fun _ acc ->
		  let te = tcst_popqv st in
		    te::acc
	      ) largs [] in
		
	      let fty = List.fold_right (
		fun hd acc ->
		  Forall (hd, acc)
	      ) largs'  ty' in

		(* and return *)
		(Ind (x, largs', ty', List.rev lcons'), fty, None)

	)


      (* term Phi *) 

      | Right (Phi (x, largs, ty, term, body)) -> (

	  (* directly return the type V largs . ty ??? *)
	  (*raise (TermCheckFailure "termcheck: Not Yet Implemented")*)
	  let (_, xty) = List.fold_right (
	    fun (x, ty, n) (i, te) ->
	      (i + 1, Forall ((x, ty, n), te))		  
	  ) largs (0, ty) in		
	    (Phi (x, largs, ty, term, body), xty, None)

	)	  

      | Left (Ast.Phi (x, largs, lty, term, body)) -> (

	  (*printf "args\n";*)

	  (* first we termcheck/input the arguments *)
	  List.fold_left (
	    fun acc (n, x, te) ->
	      let univ_fn = (fresh_name_list_name st.univ_var "univ") in
		st.univ_var <- univ_fn ++ st.univ_var;
		let (tete, tety) = termcheck st (Left te) (Some (Type (Level univ_fn))) in
		  (*
		  let b = termcheckterm2token tete st in
		  let b = token2box b 400 0 in
		    printbox b;
		  *)
		  tcst_pushqv st x tete n	    
	  ) () largs;

	  (*printf "\n\n";*)

	  (* then we typecheck ty, and finally push x as forall args . ty *)
	  let univ_fn = (fresh_name_list_name st.univ_var "univ") in
	    st.univ_var <- univ_fn ++ st.univ_var;
	    let (ltyte, ltyty) = termcheck st (Left lty) (Some (Type (Level univ_fn))) in	      

	      (*
	      printf "type\n";
	      let b = termcheckterm2token ltyte st in
	      let b = token2box b 400 0 in
		printbox b;
		printf "\n\n";
	      *)

	      tcst_pushterm st ltyte;
	      let (_, xty) = List.fold_right (
		fun (n, x, _) (i, te) ->
		  (i + 1, Forall ((x, shift_var' ((fun (_, x, _) -> x) (List.nth st.qv i)) (i + 1) (List.length largs), n), te))		  
	      ) largs (0, shift_var' ltyte (List.length largs) (List.length largs)) in		
		tcst_pushqv st x xty Explicite;		

		(*
		printf "f type\n";
		let b = termcheckterm2token xty st in
		let b = token2box b 400 0 in
		  printbox b;
		  printf "\n\n";


		printf "type\n";
		let b = termcheckterm2token (shift_var ltyte 1) st in
		let b = token2box b 400 0 in
		  printbox b;
		  printf "\n\n";
		*)

	      (* finally we typecheck all the constructors *)
		let (bodyte, bodyty) = termcheck st (Left body) (Some (shift_var ltyte 1)) in

		  (*
		printf "body\n";
		let b = termcheckres2token bodyte bodyty st in
		let b = token2box b 400 0 in
		  printbox b;
		  printf "\n\n";
		  *)

		(* TODO: verify that the term is strong normalizing *)

		(* we build the term *)

		let _ = tcst_popqv st in
		  
		let ty' = tcst_popterm st in
		  
		let largs' = List.fold_right (
		  fun _ acc ->
		    let te = tcst_popqv st in
		      te::acc
		) largs [] in
		  
		let fty = List.fold_right (
		  fun hd acc ->
		    Forall (hd, acc)
		) largs'  ty' in
		  
		(* and return *)

		let te = Phi (x, largs', ty', term, bodyte) in

		  (*
		let b = termcheckterm2token te st in
		let b = token2box b 400 0 in
		  printbox b;
		  printf "\n\n";
		  *)

		  (te, fty, None)
		    
	)

      (* term Match *) 

      | Right (Match (te, ldes, ty)) -> (

	  (Match (te, ldes, ty), ty, None)

	)	  

      (* AST Match *) 

      | Left (Ast.Match (te, ldes, retty)) -> (

	  let retty = (match retty with
			 | None -> (
			      let univ_fn2 = (fresh_name_list_name st.univ_var "univ") in
				st.univ_var <- univ_fn2 ++ st.univ_var;
				let m_tyty2 = Type (Level univ_fn2) in
				let m_ty2 = tcst_pushfv st "@match_ret_type_gen_ty2@" m_tyty2 in
				let mv2 = tcst_pushfv st "@match_ret_type_gen2@" (Var m_ty2)
				in Var (mv2)
			   )
			 | Some ty -> let (rettyte, rettyty) = termcheck st (Left ty) None in rettyte
		      ) in

	  let rettycoo = tcst_pushterm2 st retty in
    
	  (* first we typecheck te *)
	  (* NONE !!!!! *)
	  let (te', ty') = termcheck st (Left te) None in
	    (* the set of defined names *)
	  (*let defnameset = definition2nameset st.def in*)
	    (* the set of used names *)
	    (* TODO: keep the sets in state*)
	  let usedvarset = (List.fold_left (fun acc (hd, _, _) -> hd ++ acc) VarSet.empty st.qv) +++ (List.fold_left (fun acc (hd, _, _) -> hd ++ acc) VarSet.empty st.fv) in

	  let _ = tcst_pushterm2 st te' in
	  let typcoo = tcst_pushterm2 st ty' in

	  (* the alpha conversion + unification of each destructor pattern *)
	  let ldes = List.map (
	    fun hd ->
	      (* destructor pattern & body pattern vars *)
	      let vars = destructor_pattern_var (fst hd) in
		
	      (* used vars in destructor pattern *)
	      let vars_inter_usedvar = VarSet.inter vars usedvarset in
		
	      (* build alpha-conv for destructor pattern *)
	      let freshs = fresh_names2 usedvarset (VarSet.cardinal vars_inter_usedvar) "@match@" in
	      let alphai = List.combine (VarSet.elements vars_inter_usedvar) freshs in
	      let maplhai = List.map (fun (x, y) -> (y, x)) alphai in
	  
	      (* rewrite destructor pattern *)
	      let lhs = astrewrite (fst hd) (List.fold_left (fun acc (hd1, hd2) -> VarMap.add hd1 (Symb (true, hd2)) acc) VarMap.empty alphai) in
		
	      (* typechecking destructor pattern *)
	      let (lhste, lhsty) = termcheck st (Left lhs) (Some (tcst_getterm st typcoo)) in
		tcst_pushterm st lhste;
		(*
		printf "destructor pattern: ";
		let b = termcheckres2token lhste lhsty st in
		let b = token2box b 4000000 0 in
		  printbox b;
		*)
	      let s = fv lhste in

	      let listqv = List.map (
		fun hd ->
		  let ty = tcst_fvtype st hd in
		  let name = tcst_fvname st hd in		  
		  let name = (
		    try 
		      List.assoc name maplhai
		    with
		      | Not_found -> name
		  ) in
		    tcst_pushqv st name ty Explicite;
		    (*
		    printf "var:= (%s) %s: " (string_of_int hd) name;
		    let b = termcheckterm2token (shift_var ty 1) st in
		    let b = token2box b 4000000 0 in
		      printbox b;
		    *)
		      (name, hd)



	      ) (FreeVarSet.elements s) in
		
		(*
		printf "typecoo:= ";
		let b = termcheckterm2token (tcst_getterm st typcoo) st in
		let b = token2box b 4000000 0 in
		  printbox b;

		printf "rettycoo:= ";
		let b = termcheckterm2token (tcst_getterm st rettycoo) st in
		let b = token2box b 4000000 0 in
		  printbox b;
		*)

		  (* typechecking destructor body *)
		  let (rhste, rhsty) = termcheck st (Left (snd hd)) (Some (tcst_getterm st rettycoo)) in
		    (*
		    printf "destructor body: ";
		    let b = termcheckres2token rhste rhsty st in
		    let b = token2box b 4000000 0 in
		      printbox b;
		    *)

		    (* rather than returning them, we should push them 
		       such that we apply to them the subtitution *)
		  let rhste = apply_substitution_term rhste (
		    snd (
		      List.fold_left (
			fun acc hd ->
			  (fst acc + 1, 
			   ((fst acc, tcst_fvvalue st (snd hd))::(snd acc))
			  )
		      ) (0, []) (List.rev listqv)
		    )
		  ) in
		  
                  (*  
		      printf "destructor body: ";
		      let b = termcheckres2token rhste rhsty st in
		      let b = token2box b 4000000 0 in
		      printbox b;
		      printf "\n\n";
		  *)  
		  let _ = List.map (
		    fun hd ->
		      tcst_popqv st
			
		  ) (FreeVarSet.elements s) in

		  let lhste = tcst_popterm st in

		  let rhste = shift_var rhste (-(FreeVarSet.cardinal s)) in
		    tcst_pushterm st lhste;
		    tcst_pushterm st rhste;
		    ()	
	      
	  ) ldes in
	    (*
	    printf "typecoo:= ";
	    let b = termcheckterm2token (tcst_getterm st typcoo) st in
	    let b = token2box b 4000000 0 in
	      printbox b;
	    *)
	    (*
	    printf "destructed term: ";
	    let b = termcheckres2token (tcst_getterm st tecoo) (tcst_getterm st typcoo) st in
	    let b = token2box b 4000000 0 in
	      printbox b;
	    *)
	      let ldes = List.map (
		fun _ ->
		  let rhs = tcst_popterm st in
		  let lhs = tcst_popterm st in
		    (lhs, rhs)
	      ) ldes in


	      let _ = tcst_popterm st in
	      let tecoo = tcst_popterm st in
	      let retty = tcst_popterm st in

		(Match (tecoo, List.rev ldes, retty), retty, None)
			      
		  (*raise (TermCheckFailure "termcheck: Not Yet Implemented: Match")*)

   	)	  

  ) in
    let postst = st_stat st in
      if (not (postst = prest)) then (
	let b = termcheckterm2token te' st in
	let b = token2box b 4000000 0 in
	  printbox b;
	  printf "(%s, (%s))\n" 
	    (string_of_int (fst prest))
	    (String.concat "," (List.map string_of_int (snd prest)));
	  printf "(%s, (%s))\n" 
	    (string_of_int (fst postst))
	    (String.concat "," (List.map string_of_int (snd postst)));
	  raise (Failure "big probleme")
      )
      else
    (*
      printf "***********************\n";
      (match te with
      | Left te -> pprint2ast te;
      | Right te -> pprintterm te true;
      );
      printf ":\n"; flush stdout;
      (match ty with
      | None -> printf " ??\n";
      | Some ty -> pprintterm ty true;
      );
      printf "\n==>\n"; flush stdout;
      pprintterm te' true;
      printf ":\n"; flush stdout;
      pprintterm inferedty true;
      printf "***********************\n";
    *)
    tcst_pushtokens st ((Verbatim "res =") :: Newline :: (termcheckres2token te' inferedty st) :: []);
    (match ty with
       | None -> ()
       | Some ty ->
	   tcst_pushtokens st ((Verbatim "type annotation :=") :: Newline :: (termcheckterm2token ty st) :: [])
    );
    (match nty with
       | None -> ()
       | Some nty ->
	   tcst_pushtokens st ((Verbatim "truc pas clair :=") :: Newline :: (termcheckterm2token nty st) :: [])
    );     

    match (ty, nty) with
      | (None, None) -> tcst_poptokenlevel st; (te', inferedty)
      | (ty, Some ty') -> ( 
	  try
	    let (s, c) = 
	      match ty with 
		| Some ty -> unification_term ty ty' st.def
		| None -> ([], [])
	    in
	      tcst_applysubst st s;
	      st.univ_constraint <- c @ st.univ_constraint;
	      tcst_poptokenlevel st;
	      (apply_substitution_term te' s, apply_substitution_term ty' s)
	  with
	    | _ ->  
		tcst_pushtokens st ((Verbatim "cas pourri") :: []);
		tcst_poptokenlevel st; 
		(te', ty')
	)
      | (Some ty, None) ->
	  let inferedty' = extract inferedty in
	  let ty' = extract ty in
	    try ( 
	      match unification inferedty' ty' st.def with
		| Mgu (s, c) -> (
		    tcst_applysubst st s;
		    st.univ_constraint <- c @ st.univ_constraint;
		    tcst_poptokenlevel st;
		    (apply_substitution_term te' s, apply_substitution_term ty s)
		  )
		| NoMgu l -> (
		    printf "-------------------\n";
		    printf "Unification Failed\n";
		    pprintterm inferedty' true;
		    pprintterm inferedty true;
		    printf "Vs\n";
		    pprintterm ty' true;
		    pprintterm ty true;
		    printf "\n";
		    let b = termcheckres2token te' ty st in
		    let b = token2box b 4000000 0 in
		      printbox b;
		      printf "-------------------\n\n\n";
		      tcst_poptokenlevel st;
		      raise (TermCheckFailure "No unification between type annotation and infered type")

		  )
		| DnkMgu -> raise (TermCheckFailure "DK unification between type annotation and infered type")
	    ) with
	      | MshiftException ->  		  
		  tcst_pushtokens st ((Verbatim "cas pourri") :: []);
		  tcst_poptokenlevel st; 
		  (te', inferedty)
		  
;;
