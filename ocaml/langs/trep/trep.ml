open Def;;
open Misc;;
open Env;;
open Substitution;;

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

let rec unify_term_term (ctxt: env ref) (te1: term) (te2: term) : term = 
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

      | AVar (Some i), _ when not (IndexSet.mem i (fv_term te2)) ->
	let s = IndexMap.singleton i te2 in
	ctxt := subst_env (!ctxt) s;
	te1

      | _, AVar (Some i) when not (IndexSet.mem i (fv_term te1)) ->
	let s = IndexMap.singleton i te1 in
	ctxt := subst_env (!ctxt) s;
	te1

    (* constante stuff ... can be a bit tricky ... *)
      | Cste c1, Cste c2 when c1 = c2 -> Cste c1


    (* in the folowwing two cases, only definition unambiguously unfoldable to a term should be
       considered as unifyable:
       - constante refering to an Inductive, to a RecordDecl, or a unique equation 
          which might need to be rewrite as a lambda abstraction 
       N.B.: we should returns the Cste c1, or c2, as after unification their definition would have been applied to the proper substitution
    *) 
      | Cste c1, _ ->
	raise (Failure "NYI")

      | _, Cste c2 ->
	raise (Failure "NYI")

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
	(* here we should try to reduce the terms *)
	raise UnificationFail
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
  reduction of terms
  several strategy are possible:
  for beta reduction: Lazy or Eager
  possibility to have strong beta reduction
  delta: unfold equations (replace matched l.h.s. with r.h.s)
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

(*

  te must be well typed w.r.t. ctxt
*) 
let reduction (ctxt: env ref) (start: interp_strat) (te: term) : term =
  raise (Failure "NYI")
;;

(*
  typechecking

  TODO: one function per typing cases
*)

let infer (ctxt: env ref) (te: term) : term * term =
  match te with
    | Type None -> (te, Type None)
    | Type (Some u) -> (te, Type (Some (UnivSucc u)))
      (* we got a named variable *)
    | Var (Left name) -> (
      (* first we look if it's a binded variable *)
      match qv_debruijn !ctxt name with
	| Some (i, ty) -> (Var (Right i), ty)
	  (* if its not in the quantified variables, we look for declarations *)
	| None -> 
	  let s = (Name name) in
	  match declaration_type !ctxt s with
	    | None -> raise (Failure "Unknown name")
	    | Some ty -> (Cste s, ty)

    )
;;

(*
  this function push a declaration in the current ctxt
  it is typechecked, then entered in the declaration lists
  (will be used as an entry point for the RTRL (Read-Typecheck-Register loop)
   and for typechecking of Where terms
  )
  modify the ctxt
*)
let push_declaration (ctxt: env ref) (decl: declaration) : bool =
  raise (Failure "NYI")
;;


