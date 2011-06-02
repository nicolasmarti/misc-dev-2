
(*
  >= 0 -> quantified var with debruijn index
  < 0 -> free var
*)
type index = int

type name = string

type symbol = Name of name
	      | Symbol of name (* * symbol info: prefix|infix|suffix + assoc/prio *)

module SymbolMap = Map.Make(
  struct
    type t = symbol
    let compare x y = compare x y
  end
);;

type univ = UnivVar of index
	    | UnivSucc of univ (* u < UnivSucc u *)
	    | UnivMax of univ * univ (* UnivMax u1 u2 >= u1 /\ UnivMax u1 u2 >= u2 *)

type position = ((int * int) * (int * int))

let position_to_string (p: position) : string =
  let ((b1, e1), (b2, e2)) = p in
  String.concat "" [string_of_int b1; ":"; string_of_int e1; "-"; string_of_int b2; ":"; string_of_int e2; "-"]

type term = Type of univ option
	    | Var of index * name
	    | AVar of index 
	    | Cste of symbol
	    | Impl of quantifier * term
	    | Lambda of quantifier list * term
	    | Let of bool * (pattern * term) list * term
	    | If of term * term * term
	    | App of term * arg list
	    | Case of term * equation list
	    | Where of term * declaration list

	    | TyAnnotation of term * tyAnnotation
	    | SrcInfo of term * position

and equation = Guarded of pattern * (guard * term) list
	       | NotGuarded of pattern * term

and pattern = PVar of name
	      | PAVar 
	      | PCste of symbol
	      | PAlias of name * pattern
	      | PApp of symbol * (pattern * nature)

and nature = Explicit
	     | Hidden
	     | Implicit

and arg = term * nature

and quantifier = name list * tyAnnotation * nature

and guard = term

and tyAnnotation = NoAnnotation
		   | Inferred of term
		   | Annotated of term

and declaration = Signature of symbol * term
		  | Equation of equation
		  | Inductive of name * quantifier list * term * term SymbolMap.t
		  | RecordDecl of name * quantifier list * term * declaration list

type env = {
  (* quantifications (and there defined vars) *)
  mutable qv : (quantifier * (name * term) list) list;
  
  (* free variables (quantification level dependant) *)
  (* contains the type, and sum of substitution over the vars
     a fv can be pushed backward (for instance when qv is push):
       - all instance of the freevars are applied with the poped quantified variables
       - its type is quantified with Impl on the poped quantifier

     this feature allows to have typechecking conditional on providing the free variables
     (* through an interactive process reminiscent to proof mode *)

     FIXME: what to do of a free variable that is no more used ?
     
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

};;

module IndexMap = Map.Make(
  struct
    type t = int
    let compare x y = compare x y
  end
);;

(*
  ADT for errors, an exception and a composition function
*)

type trep_error = AtPos of position * trep_error
		  | FreeError of string
;;

exception TrepException of trep_error
;;

(* substitution: from free variables to term *) 
type substitution = term IndexMap.t;;

(*
  quantified free variables:
  variables which are added to the ctxt after typechecking quantifier
  (implies we really need the env)

  - needed for shifting substitution, in order to apply them bellow quantifiers / pattern
*)

(* the quantified free variables in quantifiers 
   - a fold over quantified free variables of type and patterns
*)
let rec quantifier_qfvars (q: quantifier) : name list =
  let (ps, ty, n) = q in
  List.rev ps

(* the quantified free variables in patterns 
   - all variables that have no DeBruijn Index
     * this is consistent, as the quantifier is already typed
   - all aliasing @
*)

and pattern_qfvars (p: pattern) : name list =
  match p with
    | _ -> raise (Failure "NYI")

(* quantified free variables in types (== terms) 
   - all aliasing @
*)
;;

(*
  get the size 
*)
let quantifier_fqvars_size (q: quantifier) : int =
  let (ps, ty, n) = q in
  List.length ps
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

    | Var (i, n) as v when i < 0 -> (
	try IndexMap.find i s 
	with
	  | Not_found -> v
      )

    | Cste _ as c -> c

    | Impl (q, te) -> 
	let q' = quantifier_substitution s q in
	let s' = shift_substitution s (quantifier_fqvars_size q) in
	let te' = term_substitution s' te in
	  Impl (q', te')

    | Lambda (qs, te) ->
	let (qs', s') = List.fold_left (
	  fun (hdqs, s) qs ->
	    (hdqs @ (quantifier_substitution s qs)::[],
	     shift_substitution s (quantifier_fqvars_size qs)
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


