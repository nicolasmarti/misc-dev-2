open Def;;
open Misc;;
open Env;;
open Substitution;;

open Printf;;

open Trepprinter;;

(* result of unification *)
type unification_result = Unified
			  | CannotUnified of (position * term) * (position * term) * string
			  | DontKnow of position * position

(* unification of terms 
   both terms are typed on ctxt
   this function returns the unified terms and (by side-effect) 
   the two position correspond to the terms unified
   we use (Pos.none, Pos.none) when there is no position
*)

(*
  NB: both term should not have free variables for which a subtitution exists
  (TODO: had a test + rewriting in case ???, should be better to be explicitely done on recursive calls ...)
*)

(* this exception is just for rising on defualt case *)
exception UnificationFail;;

(*
  reduction of terms
  several strategy are possible:
  for beta reduction: Lazy or Eager
  possibility to have strong beta reduction
  delta: unfold equations (replace cste with their equations)
  iota: try to match equations l.h.s
  deltaiotaweak: if after delta reduction, a iota reduction fails, then the delta reduction is backtracked
  zeta: compute the let bindings
  eta: not sure if needed

  all these different strategy are used for several cases: unification, typechecking, ...
  
*)
type strategy = 
  | Lazy 
  | Eager;;

type interp_strat = {
  strat: strategy;
  beta: bool;
  betastrong: bool;
  delta: bool;
  iota: bool;
  deltaiotaweak: bool;
  zeta: bool;
  eta: bool;
};;

let unification_strat = {
  strat = Lazy;
  beta = true;
  betastrong = false;
  delta = true;
  iota = true;
  deltaiotaweak = false;
  zeta = true;
  eta = true;
};;

(*

  te must be well typed w.r.t. ctxt
*) 
let rec reduction_term (ctxt: env ref) (start: interp_strat) (te: term) : term =
  te

and unify_term_term (ctxt: env ref) (te1: term) (te2: term) : term = 
  (*printf "(infer) %s |- %s =?= %s\n" (env2string !ctxt) (term2string te1) (term2string te2);*)
  try (

    match te1, te2 with
      (* THIS IS FALSE DUE TO THE UNIVERSE *)
      | Type _, Type _ -> Type None
	
    (* the basic rule about variables *)
      | Var (Right i), Var (Right i') when i = i' -> Var (Right i)

    (* all the rules where a free variable can be unified with a term 
       the cases span over AVar and Var
    *)
      | Var (Right i), _ when not (IndexSet.mem i (fv_term te2)) ->
	let s = IndexMap.singleton i te2 in
	ctxt := subst_env (!ctxt) s;
      (* should we rewrite subst in te2 ? a priori no:
	 1- i not in te2
	 2- if s introduce a possible substitution, it means that i was in te2 by transitives substitution
	 and that we did not comply with the N.B. above
      *)
	te2      

      | _, Var (Right i) when not (IndexSet.mem i (fv_term te1)) ->
	let s = IndexMap.singleton i te1 in
	ctxt := subst_env (!ctxt) s;
	te1

      | AVar , _ -> raise (Failure "untypedcheck term")

      | _, AVar -> raise (Failure "untypedcheck term")

      (* constante stuff ... can be a bit tricky ... *)
      | Cste c1, Cste c2 when c1 = c2 -> Cste c1

      (* for now we only support unification on equal object,
	 here equality is strict (same object in memory)
	 there are other possibility:
	 - add a method to object
	 - compare generated string representation
      *)

      | Obj o1, Obj o2 when o1 = o2 -> Obj o1

      | Impl (q1, te1), Impl (q2, te2) ->
      (* first we unify the quantifiers *)
	let q = unify_quantifier_quantifier ctxt q1 q2 in
	(* then we push q *)
	ctxt := env_push_quantifier !ctxt q;
	(* we apply all the possible subtitution to te1 and te2 *)
	let te1' = term_substitution (env_substitution !ctxt) te1 in
	let te2' = term_substitution (env_substitution !ctxt) te2 in
	(* and we unify them *)
	let te = unify_term_term ctxt te1' te2' in
	(* we get the results from poping a quantifier *)
	let (ctxt', q) = env_pop_quantifier !ctxt 1 in
	(* set the working env to the snd *)
	ctxt := ctxt';
	(* and finally returns the result *)
	Impl (q, te)

      | _ -> raise UnificationFail
  ) with
      | UnificationFail -> (
	
	(* we reduce te1 and te2 and assure that they changed *)
	let te1' = reduction_term ctxt unification_strat te1 in
	let te2' = reduction_term ctxt unification_strat te1 in
	if (te1 = te2 && te2 = te2') then raise UnificationFail;
	(* unify them *)
	let _ = unify_term_term ctxt te1' te2' in
	(* substitute in te1 *)
	term_substitution (env_substitution !ctxt) te1

      )

and unify_quantifier_quantifier (ctxt: env ref) (q1: quantifier) (q2: quantifier) : quantifier =
  let (ps1, ty1, n1) = q1 in
  let (ps2, ty2, n2) = q2 in
  (* first we need to assure that natures and patterns are equal 
     this is an aproximation, as pattern need only to be alpha equivalent ...
  *)
  if not (n1 = n2 && ps1 = ps2) then 
    raise UnificationFail
  else
    let ty = 
      match (ty1, ty2) with
	(* if ther eis NoAnnotation, it means the terms have not been typechecked *) 
	| NoAnnotation, _ -> raise UnificationFail
	| _, NoAnnotation -> raise UnificationFail
	| Infered ty1, Infered ty2 | Annotated ty1, Infered ty2 | Infered ty1, Annotated ty2 -> Infered (unify_term_term ctxt ty1 ty2)
	| Annotated ty1, Annotated ty2 -> Annotated (unify_term_term ctxt ty1 ty2)
    in
    (ps1, ty, n1)	
;;


(*
  function to grab the type of an annotation
  in case it's NoAnnotation, we create a fresh fv
*)

let get_annotation_type (ctxt: env ref) (ty: tyAnnotation) : term =
  match ty with
    | NoAnnotation -> 
      let (ctxt', fvte) = env_new_fv !ctxt (Type None) in
      ctxt := ctxt'; Var (Right fvte)
    | Annotated ty -> ty
    | Infered ty -> ty
;;

(* returns a term and a type for a name *)
let named_term (ctxt: env) (n: name) : (term * term) option =
  (* first we look if it's a binded variable *)
  match qv_debruijn ctxt n with
    | Some (i, ty) -> Some (Var (Right i), ty)
    (* if its not in the quantified variables, we look for declarations *)
    | None -> 
      let s = (Name n) in
      match declaration_type ctxt s with
	| None -> None
	| Some ty -> Some (Cste s, ty)	    
;;

(*
  typechecking

  TODO: one function per typing cases
*)


let rec infer_term (ctxt: env ref) (te: term) : term * term =
  match te with
      (* SourceInfo *)
    | SrcInfo (te, pos) -> (
      try
	infer_term ctxt te
      with
	| Failure s -> raise (Failure s)
    )
    | Type None -> (te, Type None)
    | Type (Some u) -> (te, Type (Some (UnivSucc u)))
      (* we got a named variable *)
    | Var (Left name) -> (
      match named_term !ctxt name with
	| None -> raise (Failure "Unknown name")
	| Some res -> res
    )
    (* here we have a binded variable with a Debruijn index ... *)
    | Var (Right index) when index >= 0 -> (
      let (name, ty) = qv_name !ctxt index in
      (te, ty)
    )

    | AVar -> (
      let (ctxt', fvty) = env_new_fv !ctxt (Type None) in
      ctxt := ctxt'; 
      let (ctxt', fvte) = env_new_fv !ctxt (Var (Right fvty)) in
      ctxt := ctxt'; 
      (Var (Right fvte), Var (Right fvty))
    )

    | Cste s -> (
      match declaration_type !ctxt s with
	| None -> raise (Failure "Unknown symbol")
	| Some ty -> (Cste s, ty)
    )

    | Obj o -> (Obj o, o#get_type)

    | Impl (q, te) -> (
      let (ps, _, _) = q in
      let q = typecheck_quantifier ctxt q in
      ctxt := env_push_quantifier !ctxt q;
      let (te, ty) = typecheck_term ctxt te (Type None) in
      let (ctxt', q) = env_pop_quantifier !ctxt (List.length ps) in
      ctxt := ctxt';
      (Impl (q, te), (Type None))
    )

and typecheck_term (ctxt: env ref) (te: term) (ty: term) : term * term =
  (*printf "%s |- %s :?: %s\n" (env2string !ctxt) (term2string te) (term2string ty);*)
  let (te, ty') = infer_term ctxt te in   
  ctxt := env_push_termstack !ctxt te;
  let ty'' = unify_term_term ctxt ty' ty in
  let (ctxt', te') = env_pop_termstack !ctxt in
  ctxt := ctxt';
  (te', ty'')

and typecheck_quantifier (ctxt: env ref) (q: quantifier) : quantifier =
  (* grab ps, (ty' = ) ty, nat from q*)
  (* for each p in ps:
     1) p' = typecheck p again ty'
     2) push the pattern p'
     3) ty' = shift ty' below p'
  *)
  (*
    ps' = unpop |ps| patterns
  *)
  (*
    returns (ps', ty, nat)
  *)
  let (ps, ty, nat) = q in
  let ty' = get_annotation_type ctxt ty in
  let (ty', _) = typecheck_term ctxt ty' (Type None) in
  let _ = List.fold_left (fun ty' p -> 
    let p' = typecheck_pattern ctxt p ty' in
    ctxt := env_push_pattern !ctxt p';
    shift_term ty' (List.length (List.hd (!ctxt).frames).qvs)			 
  ) ty' ps in
  let ps' = List.fold_left (fun acc hd -> 
    let (ctxt', p) = env_pop_pattern !ctxt in
    ctxt := ctxt'; p::acc
  ) [] ps in
  (ps', Infered ty', nat)

and typecheck_pattern (ctxt: env ref) (p: pattern) (ty: term) : pattern =
  match p with
    | PType u -> 
      ignore (unify_term_term ctxt (Type None) ty); p
    | PVar (n, ty') -> (
      let (ty', _) = typecheck_term ctxt ty' (Type None) in
      match named_term !ctxt n with
	(* not a constant *)
	| None | Some (Var _, _) -> 
	  let ty' = unify_term_term ctxt ty' ty in
	  PVar (n, ty')
	| Some (Cste c, ty'') ->
	  let ty' = unify_term_term ctxt ty' ty in
	  let ty' = unify_term_term ctxt ty' ty'' in
	  PCste (c, ty')
	| _ -> raise (Failure "catastrophic")	  
    )
    | PAVar ty' -> (
      let (ty', _) = typecheck_term ctxt ty' (Type None) in
      let ty' = unify_term_term ctxt ty' ty in
      PAVar ty'
    )
    | PCste _ -> raise (Failure "PCste: not yet implemented")
    | PAlias _ -> raise (Failure "PAlias: not yet implemented")
    | PApp _ -> raise (Failure "PApp: not yet implemented")


and typecheck_declaration (ctxt: env ref) (decl: declaration) : declaration =
  match decl with
    | Signature (s, ty) ->
      let (ty, _) = typecheck_term ctxt ty (Type None) in
      let decl = Signature (s, ty) in
      decl
    | _ -> raise (Failure "NYI")
;;


