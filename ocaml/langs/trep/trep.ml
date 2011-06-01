
type index = int

type name = string

type symbol = Name of name
	      | Symbol of name

type univ = UnivVar of index
	    | UnivSucc of univ
	    | UnivMax of univ * univ

type position = ((int * int) * (int * int))

type term = Type of univ option
	    | Var of index option * name option
	    | AVar of index option
	    | Cste of symbol
	    | Impl of quantifier * term
	    | Lambda of quantifier list * term
	    | Let of bool * (pattern * term) list * term
	    | If of term * term * term
	    | App of term * arg list
	    | Alias of name * term
	    | Case of term * equation list
	    | Where of term * declaration list

	    | Ind of name * arg list * term * (name * term) list
	    | Constr of int * term

	    | TyAnnotation of term * term
	    | SrcInfo of term * position

and equation = Guarded of pattern * (guard * term) list
	       | NotGuarded of pattern * term

and pattern = term

and nature = Explicit
	     | Hidden
	     | Implicit

and arg = term * nature

and quantifier = term list * tyAnnotation * nature

and guard = term

and tyAnnotation = NoAnnotation
		   | Inferred of term
		   | Annotated of term

and declaration = Signature of symbol * term
		  | Equation of equation
		  | Inductive of name * quantifier list * term * (name * term) list
		  | RecordDecl of name * quantifier list * term * declaration list

module SymbolMap = Map.Make(
  struct
    type t = symbol
    let compare x y = compare x y
  end
);;


type env = {
  (* quantifications (and there defined vars) *)
  mutable qv : (quantifier * (name * term) list) list;
  
  (* free variables (quantification level dependant) *)
  (* contains the type, and sum of substitution over the vars
     a fv can be pushed backward (for instance when qv is push), in thi case
       - all instance of the freevars are applied with the poped quantified variables
       - its type is quantified with Impl on the poped quantifier

     this feature allows to have typechecking conditional on providing the free variables
     (* through an interactive process reminiscent to proof mode *)
  *)
  mutable fv: ((term * term option) list) list;

  (* list of declaration (quantification level dependant) 
     when pushing a quantifier, they are reinput in the term through the Where construction
  *)
  mutable decl: (declaration list) list;

  (* term stack & equation stack: used by the 
     typechecker to store terms/equations already typed, such that any further unification will apply on them
     this is the responsability of the typechecker to properly pop what he has pushed
     (TODO: have an helper function that check it)
  *)
  mutable term_stack: (term list) list;

  mutable equation_stack: (equation list) list;

  (*
    list of inference rules
    used for [] quantification
  *)

  mutable inferrule: term list;

  (* list of already typed constant
     this is redundant with decl, but make easier for the type checker 
     to find the type of cste
  *)
  mutable signature : (term SymbolMap.t) list

};;

module IndexMap = Map.Make(
  struct
    type t = int
    let compare x y = compare x y
  end
);;

(* substitution: from free variables to term *) 
type substitution = term IndexMap.t;;

let quantifier_size (q: quantifier) : int =
  raise (Failure "NYI")
;;

(* application of unification to a term 

   N.B.:

   ctxt |- te :: ty

   for all x -> te' in s.
      forall ty'. ctxt |- x :: ty' <-> ctxt |- te' :: ty'

*)
let rec term_substitution (s: substitution) (te: term) : term =
  match te with
    | Type u -> Type u

    | Var (Some i, n) as v when i < 0 -> (
	try IndexMap.find i s 
	with
	  | Not_found -> v
      )
    | Var _ as v -> v

    | Cste _ as c -> c

    | Impl (q, te) -> 
	let q' = quantifier_substitution s q in
	let s' = shift_substitution s (quantifier_size q) in
	let te' = term_substitution s' te in
	  Impl (q', te')

    | Lambda (qs, te) ->
	let (qs', s') = List.fold_left (
	  fun (hdqs, s) qs ->
	    (hdqs @ (quantifier_substitution s qs)::[],
	     shift_substitution s (quantifier_size qs)
	    )
	) ([], s) qs in
	let te' = term_substitution s' te in
	  Lambda (qs', te')

    (* rmq: the definitions in let are equivalent to NotGuarded equation
       should be able to reuse some code here

       r means that the equations l.h.s. patterns are entered in one step
       with for types free variables that should be solved by unification
       when typing the bodies

       the let is a bit ambiguous: it can be either
       1) a destruction, reminiscent to case 
       2) a declaration

       choosing between both might require to have the env ...
    *)
    | Let (r, not_guard_eq, te) ->
	raise (Failure "NYI")	

    | _ -> raise (Failure "term_substitution: case not yet supported")
	
and quantifier_substitution (s: substitution) (q: quantifier) : quantifier =
  raise (Failure "NYI")

(* aging a substitution: 
   shift the quantified variable index by delta
   delta > 0 -> consider the substitution on quantified terms
   delta < 0 -> consider the substitution on less quantified terms
*)
and shift_substitution (s: substitution) (delta: int) : substitution =
  raise (Failure "NYI")
;;

(* which imply having the aging of terms 
   it returns an exception if the term has qv < delta   
*)
let shift_term (te: term) (delta: int) : term =
  raise (Failure "NYI")
;;

(* apply a substitution to a term *)
let subst_term (te: term) (s: substitution) : term =
  raise (Failure "NYI")
;;

(* applying a substitution to an environment *)
let subst_env (e: env) (s: substitution) : env =
  raise (Failure "NYI")
;;

(* result of unification *)
type unification_result = Unified
			  | CannotUnified of position * position
			  | DontKnow of position * position

(* unification of terms 
   both terms are typed on ctxt
   this function returns the unified terms and (by side-effect) 
   mutate the environment with the incrementally found substitution
   (thus depending on the case the ctxt should be copied before calling this function)
   the two position correspond to the terms unified
   we use (Pos.none, Pos.none) when there is no position
*)
let unify (ctxt: env) (te1: term) (pos1: position) (te2: term) (pos2: position) : term =
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
  warning: the context might be mutated (especially in the case of Lazy evaluation, or strong beta reduction)
  te must be well typed w.r.t. ctxt
*) 
let reduction (ctxt: env) (start: interp_strat) (te: term) : term =
  raise (Failure "NYI")
;;

(*
  typechecking
  warning: side-effect affecting the ctxt

  TODO: one function per typing cases
*)

let typecheck (ctxt: env) (te: term) (ty: term) : bool =
  raise (Failure "NYI")
;;

let infer (ctxt: env) (te: term) : term option =
  raise (Failure "NYI")
;;

(*
  grab the "pattern vars" of a terms
  warning: there is an order, so we use a list (order is the same as fv in env)
*)
let pattern_var_term (ctxt: env) (p: term) : name list =
  raise (Failure "NYI")
;;

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

let fv_term (te: term) : IndexSet.t =
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
let push_declaration (ctxt: env) (decl: declaration) : bool =
  raise (Failure "NYI")
;;


