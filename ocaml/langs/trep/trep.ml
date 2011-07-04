open Planck;;
module Pos = Position.File
;;

open Op_prec;;

(*
  >= 0 -> quantified var with debruijn index
  < 0 -> free var
*)
type index = int

type name = string

type symbol = Name of name
	      | Symbol of name * op

module SymbolMap = Map.Make(
  struct
    type t = symbol
    let compare x y = compare x y
  end
);;

type univ = UnivVar of index
	    | UnivSucc of univ (* u < UnivSucc u *)
	    | UnivMax of univ * univ (* UnivMax u1 u2 >= u1 /\ UnivMax u1 u2 >= u2 *)

type position = Pos.t * Pos.t

let noposition = (Pos.none, Pos.none)

(* object are really usefull in order to manipulate Ocaml value from trep 
   but they cannot be compiled ...
*)

open Pprinter;;

class virtual ['a] tObj =
object 
  method uuid: int = 0
  method virtual get_name: string
  method virtual get_type: 'a
  method virtual pprint: unit -> token
  method virtual apply: 'a list -> 'a
end;;

type ('a, 'b) either = Left of 'a
		       | Right of 'b
;;

type term = Type of univ option
	    | Var of (name, index) either
	    | AVar of index option
	    | Cste of symbol
	    | Obj of term tObj
	    | Impl of quantifier * term
	    | Lambda of quantifier list * term
	    | Let of bool * (pattern * term) list * term
	    | Ifte of term * term * term
	    | App of term * arg list
	    | Case of term * equation list
	    (*| Where of term * declaration list*)

	    | TyAnnotation of term * tyAnnotation
	    | SrcInfo of term * position

and equation = Guarded of pattern * (guard * term) list
	       | NotGuarded of pattern * term

and pattern = PType
	      | PVar of name
	      | PAVar 
	      | PCste of symbol
	      | PAlias of name * pattern
	      | PApp of pattern * (pattern * nature) list

and nature = Explicit
	     | Hidden
	     | Implicit

and arg = term * nature

and quantifier = pattern list * tyAnnotation * nature

and guard = term

and tyAnnotation = NoAnnotation
		   | Infered of term
		   | Annotated of term

and declaration = Signature of symbol * term
		  | Equation of equation * (* where clause *) declaration list
		  | Inductive of name * quantifier list * term * (symbol * term) list
		  | RecordDecl of name * quantifier list * term * declaration list

type env = 
{
  (* free variables (quantification level dependant) *)
  (* contains the type, and sum of substitution over the vars
     a fv can be pushed backward (for instance when qv is push):
       - all instance of the freevars are applied with the poped quantified variables
       - its type is quantified with Impl on the poped quantifier

     this feature allows to have typechecking conditional on providing the free variables
     (* through an interactive process reminiscent to proof mode *)

     FIXME: what to do of a free variable that is no more used ?
     
  *)
  (* list of declaration (quantification level dependant) 
     when pushing a quantifier, they are reinput in the term through the Where construction
  *)
  (* term stack & equation stack: used by the 
     typechecker to store terms/equations already typed, such that any further unification will apply on them
     this is the responsability of the typechecker to properly pop what he has pushed
     (TODO: have an helper function that check it)
  *)

  (* fv, decl and inferrence rule (at toplevel) *)
  fvs: (term * term option) list;
  decls: declaration list;
  inferrules: name list;

  quantified: (
    (name * term) list * (* quantified variables *)
      (term * term option) list * (* free variables *)
      
      (* stacks for different data *)
      declaration list * (* for declaration *)
      term list * (* for terms *)
      equation list * (* for equation *)
      tyAnnotation list * (* for type annotation *)
      quantifier list (* for quantifier *)

  ) list;
 
}

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
		  | UnShiftable
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

(* the quantified free variables in quantifiers *)
let rec quantifier_qfvars (q: quantifier) : name list =
  let (ps, ty, n) = q in
  List.fold_left (fun acc hd -> pattern_qfvars hd @ acc) [] ps

(* the quantified free variables in patterns 
   there is an order !!!
   (same as debruijn index)
*)

and pattern_qfvars (p: pattern) : name list =
  match p with
    | PVar n -> [n]
    | PAlias (n, p) -> n::pattern_qfvars p
    | PApp (f, arg) -> List.fold_left (fun acc hd -> pattern_qfvars hd @ acc) (pattern_qfvars f) (List.map fst arg)
    | _ -> []

;;

(*
  get the size 
*)
let quantifier_fqvars_size (q: quantifier) : int =
  List.length (quantifier_qfvars q)
;;

let pattern_fqvars_size (p: pattern) : int =
  List.length (pattern_qfvars p)
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

    | Var (Left _) -> raise (Failure "un-typechecked variable")

    | Var (Right i) as v when i < 0 -> (
	try IndexMap.find i s 
	with
	  | Not_found -> v
      )

    | Cste _ as c -> c

    | Obj _ as o -> o

    | Impl (q, te) -> 
	let (q', s') = quantifier_substitution s q in
	let te' = term_substitution s' te in
	  Impl (q', te')

    | Lambda (qs, te) ->
	let (qs', s') = List.fold_left (
	  fun (hdqs, s) qs ->
	    let (qs', s') = quantifier_substitution s qs in
	    (hdqs @ [qs'], s')
	) ([], s) qs in
	let te' = term_substitution s' te in
	  Lambda (qs', te')

    | Let (false, eqs, te) ->
      let (eqs', s') = List.fold_left (fun (eqs, s) (p, t) -> 
	let s' = shift_substitution s (pattern_fqvars_size p) in
	(eqs @ [(p, term_substitution s' t)], s')
      ) ([], s) eqs in
      Let (false, eqs', term_substitution s' te)

    | Let (true, eqs, te) ->
      let sz = List.fold_left (fun acc hd -> acc + hd) 0 (List.map (fun hd -> pattern_fqvars_size (fst hd)) eqs) in 
      let s' = shift_substitution s sz in
      Let (true,
	   List.map (fun (p, t) -> (p, term_substitution s' t)) eqs,
	   term_substitution s' te
      )

    | Ifte (t1, t2, t3) ->
      Ifte (term_substitution s t1,
	    term_substitution s t2,
	    term_substitution s t3
      )

    | App (f, args) ->
      App (term_substitution s f,
	   List.map (fun (t, n) -> (term_substitution s t, n)) args
	   )

    | Case (te, eqs) ->
      Case (term_substitution s te,
	    List.map (fun hd -> equation_substitution s hd) eqs
      )
(*
    | Where (te, decls) ->
      Where (term_substitution s te,
	    List.map (fun hd -> declaration_substitution s hd) decls
      )
*)
    | TyAnnotation (te, ty) ->
      TyAnnotation (term_substitution s te,
		    tyAnnotation_substitution s ty)

    | SrcInfo (te, pos) ->
      SrcInfo (term_substitution s te,
	       pos)

    | _ -> raise (Failure "term_substitution: case not yet supported")
	
and quantifier_substitution (s: substitution) (q: quantifier) : quantifier * substitution =
  let (qs, ty, n) = q in
  let s' = shift_substitution s (quantifier_fqvars_size q) in
  let ty' = tyAnnotation_substitution s' ty in
  (qs, ty', n), s'

and tyAnnotation_substitution (s: substitution) (ty: tyAnnotation) : tyAnnotation =
    match ty with
      | NoAnnotation -> NoAnnotation
      | Infered ty -> Infered (term_substitution s ty)
      | Annotated ty -> Annotated (term_substitution s ty)
      
and equation_substitution (s: substitution) (eq: equation) : equation =
  match eq with
    | Guarded (p, gtes) ->
      let s' = shift_substitution s (pattern_fqvars_size p) in
      Guarded (p,
	       List.map (fun (g, t) -> term_substitution s' g, term_substitution s' t) gtes
      )
    | NotGuarded (p, t) -> 
      let s' = shift_substitution s (pattern_fqvars_size p) in
      NotGuarded (p, term_substitution s' t)

and declaration_substitution (s: substitution) (decl: declaration) : declaration =
  match decl with
    | Signature (symb, te) ->
      Signature (symb, term_substitution s te)

    | Equation (eq, decls) -> Equation (equation_substitution s eq, List.map (declaration_substitution s) decls)

    | Inductive (n, args, ty, constrs) ->
      let (args', s') = List.fold_left (fun (args, s) hd -> 
	let (hd', s') = quantifier_substitution s hd in
	(args @ [hd'], s')
      ) ([], s) args in
      let ty' = term_substitution s' ty in
      let constrs' = List.map (fun (symb, ty) -> symb, term_substitution s' ty) constrs in
      Inductive (n, args', ty', constrs')
 
    | RecordDecl (n, args, ty, decls) ->
      let (args', s') = List.fold_left (fun (args, s) hd -> 
	let (hd', s') = quantifier_substitution s hd in
	(args @ [hd'], s')
      ) ([], s) args in
      let ty' = term_substitution s' ty in
      let decls' = List.map (fun hd -> declaration_substitution s' hd) decls in
      RecordDecl (n, args', ty', decls')


(* aging a substitution: 
   shift the quantified variable index by delta
   delta > 0 -> consider the substitution on quantified terms
   delta < 0 -> consider the substitution on less quantified terms
*)
(* val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b *)
and shift_substitution (s: substitution) (delta: int) : substitution =
  IndexMap.fold (fun key value acc -> 
    try 
      IndexMap.add key (shift_term value delta) acc
    with
      | TrepException UnShiftable -> acc
  ) s IndexMap.empty

(* which imply having the aging of terms 
   it returns an exception if the term has qv < delta   
*)
and shift_term (te: term) (delta: int) : term =
  leveled_shift_term te 0 delta
  
and leveled_shift_term (te: term) (level: int) (delta: int) : term =
  match te with
    | Type u -> Type u

    | Var (Left _) -> raise (Failure "untypechecked variable")

    | Var (Right i) as v when i < 0 -> v
      
    | Var (Right i) as v ->
      if i >= level then
	if i + delta < level then
	  raise (TrepException UnShiftable)
	else
	  Var (Right (i + level))
      else
	v

    | AVar None -> raise (Failure "AVar untypechecked")

    | AVar i as v -> v

    | Cste _ as c -> c

    | Obj _ as o -> o

    | Impl (q, te) ->
      let (q', level') = leveled_shift_quantifier q level delta in
      let te' = leveled_shift_term te level' delta in
      Impl (q', te')

    | Lambda (qs, te) ->
      let (qs', level') = List.fold_left (fun (qs, level) q ->
	let (q', level') = leveled_shift_quantifier q level delta in
	(qs @ [q'], level')
      ) ([], level) qs in
      Lambda (qs', leveled_shift_term te level' delta)

    | Let (false, eqs, te) ->
      let (eqs', level') = List.fold_left (fun (eqs, level) (p, t) ->
	let level' = level + (pattern_fqvars_size p) in
	(eqs @ [(p, leveled_shift_term t level' delta)], level')
      ) ([], level) eqs in
      Let (false, eqs', leveled_shift_term te level' delta)
      
    | Let (true, eqs, te) ->
      let sz = List.fold_left (fun acc hd -> acc + hd) 0 (List.map (fun hd -> pattern_fqvars_size (fst hd)) eqs) in 
      let level' = level + sz in
      Let (true,
	   List.map (fun (p, t) -> (p, leveled_shift_term t level' delta)) eqs,
	   leveled_shift_term te level' delta
      )

    | Ifte (t1, t2, t3) ->
      Ifte (leveled_shift_term t1 level delta,
	    leveled_shift_term t2 level delta,
	    leveled_shift_term t3 level delta
      )

    | App (f, args) ->
      App (leveled_shift_term f level delta,
	   List.map (fun (t, n) -> (leveled_shift_term t level delta, n)) args
	   )

    | Case (te, eqs) ->
      Case (leveled_shift_term te level delta,
	    List.map (fun hd -> leveled_shift_equation hd level delta) eqs
      )
(*
    | Where (te, decls) ->
      Where (leveled_shift_term te level delta,
	    List.map (fun hd -> leveled_shift_declaration hd level delta) decls
      )
*)
    | TyAnnotation (te, ty) ->
      TyAnnotation (leveled_shift_term te level delta,
		    leveled_shift_tyAnnotation ty level delta)

    | SrcInfo (te, pos) ->
      SrcInfo (leveled_shift_term te level delta,
	       pos)

and shift_quantifier (q: quantifier) (delta: int) : quantifier * int =
  leveled_shift_quantifier q 0 delta

and leveled_shift_quantifier (q: quantifier) (level: int) (delta: int) : quantifier * int =
  let (ps, ty, n) = q in
  let sz = quantifier_fqvars_size q in
  let level' = level + sz in
  (ps, leveled_shift_tyAnnotation ty level' delta, n), level'

and shift_tyAnnotation (ty: tyAnnotation) (delta: int) : tyAnnotation =
  leveled_shift_tyAnnotation ty 0 delta

and leveled_shift_tyAnnotation (ty: tyAnnotation) (level: int) (delta: int) : tyAnnotation =
  match ty with
    | NoAnnotation -> NoAnnotation
    | Infered ty -> Infered (leveled_shift_term ty level delta)
    | Annotated ty -> Annotated (leveled_shift_term ty level delta)

and shift_equation (eq: equation) (delta: int) : equation =
  leveled_shift_equation eq 0 delta

and leveled_shift_equation (eq: equation) (level: int) (delta: int) : equation =
  match eq with
    | Guarded (p, gtes) ->
      let level' = level + (pattern_fqvars_size p) in
      Guarded (p,
	       List.map (fun (g, t) -> leveled_shift_term g level' delta, leveled_shift_term t level' delta) gtes
      )
    | NotGuarded (p, t) -> 
      let level' = level + (pattern_fqvars_size p) in
      NotGuarded (p, leveled_shift_term t level' delta)

and shift_declaration (decl: declaration) (delta: int) : declaration =
  leveled_shift_declaration decl 0 delta

and leveled_shift_declaration (decl: declaration) (level: int) (delta: int) : declaration =
  match decl with
    | Signature (symb, te) ->
      Signature (symb, leveled_shift_term te level delta)

    | Equation (eq, decls) -> Equation (leveled_shift_equation eq level delta, List.map (fun hd -> leveled_shift_declaration hd level delta) decls)

    | Inductive (n, args, ty, constrs) ->
      let (args', level') = List.fold_left (fun (args, level) hd -> 
	let (hd', level') = leveled_shift_quantifier hd level delta in
	(args @ [hd'], level')
      ) ([], level) args in
      let ty' = leveled_shift_term ty level' delta in
      let constrs' = List.map (fun (symb, ty) -> symb, leveled_shift_term ty level' delta) constrs in
      Inductive (n, args', ty', constrs')
 
    | RecordDecl (n, args, ty, decls) ->
      let (args', level') = List.fold_left (fun (args, level) hd -> 
	let (hd', level') = leveled_shift_quantifier hd level delta in
	(args @ [hd'], level')
      ) ([], level) args in
      let ty' = leveled_shift_term ty level' delta in
      let decls' = List.map (fun hd -> leveled_shift_declaration hd level' delta) decls in
      RecordDecl (n, args', ty', decls')

;;

(* applying a substitution to an environment *)
let subst_env (e: env) (s: substitution) : env =
  let (q', s') = List.fold_left (fun (q, s) (qv, fv, decl, tstack, eqstack, tystack, qstack) ->
    let fv' = List.map (fun (hd1, hd2) -> (term_substitution s hd1,
					  match hd2 with
					    | None -> None 
					    | Some hd2 -> Some (term_substitution s hd2)
    )
    ) fv in
    let decl' = List.map (fun hd -> declaration_substitution s hd) decl in
    let tstack' = List.map (term_substitution s) tstack in
    let eqstack' = List.map (equation_substitution s) eqstack in
    let tystack' = List.map (tyAnnotation_substitution s) tystack in
    let s' = shift_substitution s (- (List.length qv)) in
    (* the types in qv and quantifiers are not in the scope of qv vars, but bellow *)
    let (qstack', _) = List.split (List.map (quantifier_substitution s') qstack) in
    let qv' = List.map (fun (hd1, hd2) -> (hd1, term_substitution s' hd2)) qv in
    (q @ [qv', fv', decl', tstack', eqstack', tystack', qstack'], s')
  ) ([], s) e.quantified in
  let fvs' = List.map (fun (hd1, hd2) -> (term_substitution s' hd1,
					  match hd2 with
					    | None -> None 
					    | Some hd2 -> Some (term_substitution s' hd2)
  )
  ) e.fvs in
  let decls' = List.map (fun hd -> declaration_substitution s' hd) e.decls in
  {
    fvs = fvs';
    decls = decls';
    inferrules = e.inferrules;
    quantified = q';
  } 
;;

(* the environment is itself reminiscent of a substitution: 
   it should be applied only to a term that typecheck in the environment
*)
let fvs_substitution (l: (term * term option) list) (startindex: int): (int * substitution) = 
  List.fold_right (fun (ty, s) (i, acc) ->
    match s with
      | None -> (i - 1, acc)
      | Some s -> (i - 1, IndexMap.add i s acc)
  ) l (startindex, IndexMap.empty)
;;

let env_substitution (e: env) : substitution =
  let (_, s) = List.fold_right (fun hd (i, acc) ->
    let (_, fvs, _, _, _, _, _) = hd in
    let (i', s') = fvs_substitution fvs i in
    (i', IndexMap.merge (fun k valacc vals ->
      match valacc, vals with
	| None, None -> raise (Failure "Catastrophic: in env_substitution, both substitution have no data for a given key")
	| Some v1, Some v2 ->  raise (Failure "Catastrophic: in env_substitution, both substitution have a data for a given key")
	| Some v1, None -> Some v1
	| None, Some v2 -> Some v2
     ) acc s')
    
  ) e.quantified (fvs_substitution e.fvs (-1)) in
  s
;; 

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

let fv_term (te: term) : IndexSet.t =
  raise (Failure "NYI")
;;


(*
  NB: both term should not have free variables for which a subtitution exists
  (TODO: had a test + rewriting in case ???, should be better to be explicitely done on recursive calls ...)
*)
let unify (ctxt: env ref) (te1: term) (pos1: position) (te2: term) (pos2: position) : term =
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
      (* should we rewrite subst in s2 ? a priori no:
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

    | _ -> raise (Failure "NYI")
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


