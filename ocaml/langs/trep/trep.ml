open Def;;

(*
  quantified free variables:
  variables which are added to the ctxt after typechecking quantifier
  (implies we really need the env)

  - needed for shifting substitution, in order to apply them bellow quantifiers / pattern
*)

(* the quantified free variables in quantifiers *)
let rec quantifier_qfvars (q: quantifier) : (name * term) list =
  let (ps, ty, n) = q in
  List.fold_left (fun acc hd -> pattern_qfvars hd @ acc) [] ps

(* the quantified free variables (together with there type) in patterns 
   there is an order !!!
   (same as debruijn index)
*)

and pattern_qfvars (p: pattern) : (name * term) list =
  match p with
    | PVar (n, ty) -> [(n, ty)]
    | PAlias (n, p, ty) -> (n, ty)::pattern_qfvars p
    | PApp (f, arg, _) -> List.fold_left (fun acc hd -> pattern_qfvars hd @ acc) (pattern_qfvars f) (List.map fst arg)
    | _ -> []

;;

(* push a (typed) pattern / frame in an environment *)
let env_push_pattern (ctxt: env) (p: pattern) : env =
  let l = pattern_qfvars p in
  { ctxt with frames = {empty_frame with qvs = l; pattern = p}::ctxt.frames }
;;

(* pop a pattern / frame from the environment *)
let rec env_pop_pattern (ctxt: env) : env * pattern =
  match ctxt.frames with
    (* for poping, here, we need to have a "clean" frame *)
    (* extension: accept a list of free variable,
       abstract l in the free vars, 
       return a substitution, from the free var, to app of freevar to l       
    *)
    | { qvs = l;
	pattern = p;
	fvs = [];
	decls = [];
	terms = [];
	equations = [];
	annotations = [];
	natures = [];
      }::tl -> 
      ({ctxt with frames = tl}, p)
    | _ -> raise (Failure "Case not yet supported")
;;

let env_push_termstack (ctxt: env) (te: term) : env =
  match ctxt.frames with
    | hd::tl  ->
      {ctxt with frames = {hd with terms = te::hd.terms}::tl}
    | _ -> raise (Failure "Catastrophic: empty frame list")
;;

let env_pop_termstack (ctxt: env) : env * term =
  match ctxt.frames with
    | hd::tl -> (
      match hd.terms with
	| thd::ttl ->	  
	  ({ctxt with frames = {hd with terms = ttl}::tl}, thd)
	| _ -> raise (Failure "Catastrophic: no term to pop")
    )
    | _ -> raise (Failure "Catastrophic: empty frame list")
;;

let env_push_annotation (ctxt: env) (ty: tyAnnotation) : env =
  match ctxt.frames with
    | hd::tl  ->
      {ctxt with frames = {hd with annotations = ty::hd.annotations}::tl}
    | _ -> raise (Failure "Catastrophic: empty frame list")
;;

let env_pop_annotation (ctxt: env) : env * tyAnnotation =
  match ctxt.frames with
    | hd::tl -> (
      match hd.annotations with
	| thd::ttl ->	  
	  ({ctxt with frames = {hd with annotations = ttl}::tl}, thd)
	| _ -> raise (Failure "Catastrophic: no annotation to pop")
    )
    | _ -> raise (Failure "Catastrophic: empty frame list")
;;

let env_push_nature (ctxt: env) (n: nature) : env =
  match ctxt.frames with
    | hd::tl  ->
      {ctxt with frames = {hd with natures = n::hd.natures}::tl}
    | _ -> raise (Failure "Catastrophic: empty frame list")
;;

let env_pop_nature (ctxt: env) : env * nature =
  match ctxt.frames with
    | hd::tl -> (
      match hd.natures with
	| thd::ttl ->	  
	  ({ctxt with frames = {hd with natures = ttl}::tl}, thd)
	| _ -> raise (Failure "Catastrophic: no nature to pop")
    )
    | _ -> raise (Failure "Catastrophic: empty frame list")
;;

(* push a (typed) quantifier in an environment *)
let env_push_quantifier (ctxt: env) (q: quantifier) : env =
  (* we grab the patterns, and type annotation *)
  let (ps, ty, n) = q in
  (* we push the annotation *)
  let ctxt = env_push_annotation ctxt ty in
  let ctxt = env_push_nature ctxt n in
  List.fold_left env_push_pattern ctxt ps
;;

let rec fold_leftn (f: 'b -> 'b) (acc: 'b) (n: int) : 'b =
  if n < 0 then
    acc
  else
    fold_leftn f (f acc) (n-1)
;; 

(* pop a quantifier from an environment *)
let rec env_pop_quantifier (ctxt: env) (size: int) : env * quantifier =
  let (ctxt, ps) = fold_leftn (fun (ctxt, ps) ->
    let (ctxt, p) = env_pop_pattern ctxt in
    (ctxt, p::ps)
  ) (ctxt, []) size in
  let (ctxt, ty) = env_pop_annotation ctxt in
  let (ctxt, n) = env_pop_nature ctxt in
  (ctxt, (ps, ty, n))  
;;

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
		  | UnTypeckedTerm of term
;;

exception TrepException of trep_error
;;

(*TODO: properly raise exception *)

(* substitution: from free variables to term *) 
type substitution = term IndexMap.t;;

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
  let ty' = tyAnnotation_substitution s ty in
  let (qs', s') = patterns_substitution s qs in
  (qs', ty', n), s'

and tyAnnotation_substitution (s: substitution) (ty: tyAnnotation) : tyAnnotation =
    match ty with
      | NoAnnotation -> NoAnnotation
      | Infered ty -> Infered (term_substitution s ty)
      | Annotated ty -> Annotated (term_substitution s ty)
      
and equation_substitution (s: substitution) (eq: equation) : equation =
  match eq with
    | Guarded (p, gtes) ->
      let (p', s') = pattern_substitution s p in
      Guarded (p',
	       List.map (fun (g, t) -> term_substitution s' g, term_substitution s' t) gtes
      )
    | NotGuarded (p, t) -> 
      let (p', s') = pattern_substitution s p in
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

and pattern_substitution (s: substitution) (p: pattern) : (pattern * substitution) =
  raise (Failure "NYI")

and patterns_substitution (s: substitution) (p: pattern list) : (pattern list * substitution) =
  raise (Failure "NYI")

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
  let (ps', level') = leveled_shift_patterns ps level delta in
  (ps', leveled_shift_tyAnnotation ty level delta, n), level'

and leveled_shift_patterns (ps: pattern list) (level: int) (delta: int) : pattern list * int =
  raise (Failure "NYI")

and leveled_shift_pattern (ps: pattern) (level: int) (delta: int) : pattern * int =
  raise (Failure "NYI")

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
      let (p', level') = leveled_shift_pattern p level delta in
      Guarded (p',
	       List.map (fun (g, t) -> leveled_shift_term g level' delta, leveled_shift_term t level' delta) gtes
      )
    | NotGuarded (p, t) -> 
      let (p', level') = leveled_shift_pattern p level delta in
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
  let (frames, _) = List.fold_left (fun (fs, s) f ->
    (* s' is the substitution shift to the upper frame level *)
    let s' = shift_substitution s (- (List.length f.qvs)) in
    ({ qvs = List.map (fun (hd1, hd2) -> (hd1, term_substitution s' hd2)) f.qvs;
       pattern = fst (pattern_substitution s' f.pattern);
       fvs = List.map (fun (hd1, hd2) -> (term_substitution s hd1,
					  match hd2 with
					    | None -> raise (Failure "something crippled with environment, should have more flexible info on indices of qvs & fvs")
					    | Some hd2 -> Some (term_substitution s hd2)
       )) f.fvs;
       decls = List.map (fun hd -> declaration_substitution s hd) f.decls;
       terms = List.map (term_substitution s) f.terms;
       equations = List.map (equation_substitution s) f.equations;
       annotations = List.map (tyAnnotation_substitution s) f.annotations;
       natures = f.natures      
    }::fs, s'
    )
  ) ([], s) e.frames
  in
  { e with frames = frames }
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
(*
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
  s*)
  raise (Failure "TOREDO")
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


