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
  grab the freevariables of a term
  no needs for order, so we use a set
*)
module IndexSet = Set.Make(
  struct
    type t = int
    let compare x y = compare x y
  end
);;

let rec fv_term (te: term) : IndexSet.t =
  match te with
    | Type u -> IndexSet.empty
    | Var (Right i) when i < 0 -> IndexSet.singleton i
    | Var (Right i) when i >= 0 -> IndexSet.empty
    | AVar (Some i) -> IndexSet.singleton i
    | Cste c -> raise (Failure "NYI")
    | Obj o -> IndexSet.empty
    | Impl (q, te) -> IndexSet.union (fv_quantifier q) (fv_term te)
    | Lambda (qs, te) -> 
      List.fold_left (fun acc hd -> 
	IndexSet.union acc (fv_quantifier hd)
      ) (fv_term te) qs
    | Let (_, defs, te) ->
      List.fold_left (fun acc (_, hd) -> 
	IndexSet.union acc (fv_term hd)
      ) (fv_term te) defs
    | Ifte (t1, t2, t3) ->
      IndexSet.union (fv_term t1) (IndexSet.union (fv_term t2) (fv_term t3))
    | App (f, args) ->
      List.fold_left (fun acc (hd, _) -> 
	IndexSet.union acc (fv_term hd)
      ) (fv_term f) args
    | Case (te, eqs) ->
      List.fold_left (fun acc hd -> 
	IndexSet.union acc (fv_equation hd)
      ) (fv_term te) eqs
    | TyAnnotation (te, ty) ->
      IndexSet.union (fv_term te) (fv_tyAnnotation ty)
    | SrcInfo (te, _) -> fv_term te
    | _ -> raise (Failure "fv_term: not supported term")

and fv_quantifier (q: quantifier) : IndexSet.t =
  let (_, ty, _) = q in
  fv_tyAnnotation ty
and fv_tyAnnotation (ty: tyAnnotation) : IndexSet.t =
  match ty with
    | NoAnnotation -> IndexSet.empty
    | Infered te | Annotated te -> fv_term te
and fv_equation (eq: equation) : IndexSet.t =
  match eq with
    | NotGuarded (p, te) -> fv_term te
    | Guarded (p, dess) ->
      List.fold_left (fun acc (_, hd) ->
	IndexSet.union acc (fv_term hd)
      ) IndexSet.empty dess      
;;


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
  raise (Failure "NYI")
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

let typecheck (ctxt: env ref) (te: term) (ty: term) : bool =
  raise (Failure "NYI")
;;

let infer (ctxt: env ref) (te: term) : term option =
  raise (Failure "NYI")
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


