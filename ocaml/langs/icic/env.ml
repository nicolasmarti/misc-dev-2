open Term;;
open Varmap;;
open Varset;;
open Universe;;
open Definition;;
open Pprinter;;
open Fm;;
open Freshness;;
open Printf;;
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
  mutable fv: (name * term option) list;  

  mutable s: substitution;

  (* substituable variable, only used for substitution *)
  mutable sv: FreeVarSet.t;

  mutable sizeeq : bexpr list;

  mutable destructeq : (term * term) list;

  mutable univ_var: VarSet.t;

  mutable univ_constraint: univ_level_constraint list;

  mutable term_storage: (term list) list;

  mutable def: (term * term * defnature) definition;

  oracles: (typechecker_state -> term -> term option) list;

  coercion: ((term * term) * term) list;

  mutable tc_tree: token list list;

};;

let tcst_applysubst (st: typechecker_state) (s: substitution) : unit =
  let (_, qv') =  (List.fold_left (
			   fun (s', l1) (x, te, n) ->
			     let s'' = shift_var_substitution s' (-1) in
			     let te' = apply_substitution_term te s'' in
			       (s'', (x, te', n)::l1)			
			 ) (s, []) st.qv
			) in
  let (_, stck) =  (List.fold_left (
		      fun (s', l2) lt ->
			let lt' = apply_substitution_listterm lt s' in
			let s'' = shift_var_substitution s' (-1) in
			  (s'', lt'::l2)			
		    ) (s, []) (st.term_storage)
		   ) in
    st.qv <- List.rev qv';
    st.term_storage <- List.rev stck;
    st.fv <-  List.map (fun (hd1, hd2) -> 
			  (hd1,
			   (match hd2 with
			      | None -> None
			      | Some hd2 -> Some (apply_substitution_term hd2 s)
			   )  
			  )			 
		       ) st.fv;
    st.s <- compose_substitution st.s s
    (* there is no substitution for destructeq *)
;;

let tcst_pushterm (st: typechecker_state) (t: term) : (int * int) =
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
    | e -> printf "tcst_getterm:"; raise e
;;

let tcst_qvtype (st: typechecker_state) (v: int) : term =
  try (
    if (v < 0 || v >= List.length st.qv) then
      raise (Failure "No such qv")
    else
      let t = (fun (_, te, _) -> te) (List.nth st.qv v) in
	shift_var t (v + 1)    
  ) with
    | e -> printf "tcst_qvtype:"; raise e
;;

let tcst_qvnature (st: typechecker_state) (v: int) : nature =
  try (
    if (v < 0 || v >= List.length st.qv) then
      raise (Failure "No such qv")
    else
      (fun (_, _, n) -> n) (List.nth st.qv v)
  ) with
    | e -> printf "tcst_qvnature:"; raise e
;;

let tcst_fvtype (st: typechecker_state) (v: int) : term =
  try (
    match List.nth st.fv (List.length st.fv + v) with
      | (_, None) -> raise (Failure "fv is no more active")
      | (_, Some te) -> te
  ) with
    | e -> printf "tcst_fvtype:"; raise e
;;

(*
let tcst_fvvalue (st: typechecker_state) (v: int) : term =
  try (
    match List.nth st.fv (List.length st.fv + v) with
      | (_, Some _) -> v
      | _ -> raise (Failure "fv is no more active")
  ) with
    | e -> (*printf "tcst_fvtype:";*) raise e
;;
*)
let tcst_fvname (st: typechecker_state) (v: int) : name =
  try (
    match List.nth st.fv (List.length st.fv + v) with
      | (n, _) -> n
  ) with
    | e -> printf "tcst_fvname:"; raise e
;;

let tcst_vartype (st: typechecker_state) (v: int) : term =
  if (v < 0) then
    tcst_fvtype st v
  else
    tcst_qvtype st v
;;

let tcst_varval (st: typechecker_state) (v: int) : term =
  try 
    FreeVarMap.find v st.s
  with
    | not_found -> TVar v
;;

let tcst_pushqv (st: typechecker_state) (x: string) (ty: term) (n: nature) : unit =
  st.qv <- (x, ty, n)::st.qv;
  st.fv <- List.map (fun (hd1, hd2) -> 
		       (hd1,
			(match hd2 with
			  | None -> None
			  | Some hd2 -> Some (shift_var hd2 1)
			)
		       )
		    ) st.fv;
  st.term_storage <- ([])::st.term_storage;
  st.s <- shift_var_substitution st.s 1;
  st.sv <- FreeVarSet.fold (
    fun hd acc ->
      if (hd < 0) then 
	FreeVarSet.add hd acc
      else
	FreeVarSet.add (hd + 1) acc
  ) st.sv FreeVarSet.empty
;;

let tcst_popqv (st: typechecker_state) (t: term) : ((string * term * nature) * term) =
  let res = List.hd st.qv in
    st.fv <- List.map (fun (hd1, hd2) -> 
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
			  )
			 )
		      ) st.fv;
    st.qv <- List.tl st.qv;
    st.term_storage <- List.tl st.term_storage;
    st.sv <- FreeVarSet.fold (
      fun hd acc ->
	if (hd < 0) then 
	  FreeVarSet.add hd acc
	else
	  if (hd - 1 < 0) then acc
	  else FreeVarSet.add (hd - 1) acc
    ) st.sv FreeVarSet.empty;
    let (good, bad) = shift_var_substitution_err st.s (-1) in
      st.s <- good;
      (res, apply_substitution_term t bad)
;;

let tcst_popqv2 (st: typechecker_state) : (string * term * nature) =
  let res = List.hd st.qv in
    st.fv <- List.map (fun (hd1, hd2) -> 
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
			  )
			 )
		      ) st.fv;
    st.qv <- List.tl st.qv;
    st.term_storage <- List.tl st.term_storage;
    st.sv <- FreeVarSet.fold (
      fun hd acc ->
	if (hd < 0) then 
	  FreeVarSet.add hd acc
	else
	  if (hd - 1 < 0) then acc
	  else FreeVarSet.add (hd - 1) acc
    ) st.sv FreeVarSet.empty;
    let (good, bad) = shift_var_substitution_err st.s (-1) in
      st.s <- good;
      res
;;

let tcst_popqv3 (st: typechecker_state) : ((string * term * nature) * term list) =
  let res = List.hd st.qv in
    st.fv <- List.map (fun (hd1, hd2) -> 
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
			  )
			 )
		      ) st.fv;
    st.qv <- List.tl st.qv;
    let hd = List.hd st.term_storage in
      st.term_storage <- List.tl st.term_storage;
      st.sv <- FreeVarSet.fold (
	fun hd acc ->
	  if (hd < 0) then 
	    FreeVarSet.add hd acc
	  else
	    if (hd - 1 < 0) then acc
	    else FreeVarSet.add (hd - 1) acc
      ) st.sv FreeVarSet.empty;
      let (good, bad) = shift_var_substitution_err st.s (-1) in
	st.s <- good;
	(res, hd)
;;

let tcst_pushfv (st: typechecker_state) (n: name) (ty: term) : int =
  st.fv <- (n, Some ty)::st.fv;
  (- (List.length st.fv))
;;


let tcst_addconstraint (st: typechecker_state) (uc: univ_level_constraint list) =
  st.univ_var <- List.fold_left (fun acc hd ->
				   acc +++ (ulc_var hd)
				) st.univ_var uc;
  st.univ_constraint <- st.univ_constraint @ uc
;;

let tcst_subst (st: typechecker_state) (te: term) : term =
  apply_substitution_term te st.s
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

let tcst_add_fv (st: typechecker_state) : int =
  let univ_fn1 = (fresh_name_list_name st.univ_var "univ") in
    st.univ_var <- univ_fn1 ++ st.univ_var;
    let m_tyty1 = TType (Level univ_fn1) in
    let m_ty1 = tcst_pushfv st "@ty@" m_tyty1 in
    let mv1 = tcst_pushfv st "@te@" (TVar m_ty1) in
      mv1
;;

let tcst_freshuniv (st: typechecker_state) =
  let univ_fn1 = (fresh_name_list_name st.univ_var "univ") in
    st.univ_var <- univ_fn1 ++ st.univ_var;
    Level univ_fn1    
;;

let empty_typechecker_st () = {
  qv = [];
  fv = [];
  s = FreeVarMap.empty;
  sv = FreeVarSet.empty;
  sizeeq = [];
  destructeq = [];
  univ_var = VarSet.empty;
  univ_constraint = [];
  term_storage = ([])::[];
  def = (DefLeaf VarMap.empty);
  oracles = [];
  coercion = [];
  tc_tree = [];
}
;;

let reinit_typechecker_st st =
  st.qv <- [];
  st.fv <- [];
  st.s <- FreeVarMap.empty;
  st.sv <- FreeVarSet.empty;
  st.term_storage <- ([])::[];
  st.tc_tree <- [];
;;

let init_sv st =
  st.sv <- snd (List.fold_left (
		  fun acc hd ->
		    match hd with
		      | (_, Some _) -> (fst acc - 1, FreeVarSet.add (fst acc) (snd acc))
		      | _ -> (fst acc - 1, snd acc)
		) (-1, FreeVarSet.empty) (List.rev st.fv)
	       )
;;
		  
let env2token (st: typechecker_state) : token =

  let qv = Box (
    (intercalate (Verbatim "") (snd (
				   List.fold_left (
				     fun acc hd ->
				       (hd :: (fst acc), 
					(snd acc) @ Newline :: (Verbatim "(") :: (Verbatim ((fun (n, _, _) -> n) hd)) :: (Verbatim ":") :: (Space 1) :: (let t = term2token ((fun (_, ty, _) -> ty) hd) false (List.map (fun (n, _, _) -> n) (fst acc)) in Box t) :: (Verbatim ")") :: []
				       )
				   ) ([], []) (List.rev st.qv)
				 )
				)
    )
  ) in
  let lv = List.map (fun (n, _, _) -> n) $ st.qv in
  let s = 
    Box(
      (FreeVarMap.fold (
	 fun key value acc ->
	   acc @ [Newline; Verbatim (string_of_int key); Space 1; Verbatim "=>"; Space 1] @ (term2token value false lv)
       ) st.s []
      )
    ) in
    Box [Verbatim "{"; Newline; Verbatim "qv := "; qv; Newline; Verbatim "s := "; s; Newline; Verbatim "}"; Newline]
;;

let copy_env (e: typechecker_state) :  typechecker_state =
  let st =  empty_typechecker_st () in
    st.qv <- e.qv;
    st.fv <- e.fv;
    st.s <- e.s;
    st.sv <- e.sv;
    st.sizeeq <- e.sizeeq;
    st.destructeq <- e.destructeq;
    st.univ_var <- e.univ_var;
    st.univ_constraint <- e.univ_constraint;
    st.term_storage <- e.term_storage;
    st.def <- e.def;
    st.tc_tree <- e.tc_tree;
    st
;;
