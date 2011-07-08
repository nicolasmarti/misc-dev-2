open Def;;
open Misc;;

(* substitution: from free variables to term *) 
type substitution = term IndexMap.t;;

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
	let (p', s') = pattern_substitution s p in
	(eqs @ [(p', term_substitution s' t)], s')
      ) ([], s) eqs in
      Let (false, eqs', term_substitution s' te)

    | Let (true, eqs, te) ->
      let sz = List.fold_left (fun acc hd -> acc + hd) 0 (List.map (fun hd -> pattern_fqvars_size (fst hd)) eqs) in 
      let s' = shift_substitution s sz in
      Let (true,
	   List.map (fun (p, t) -> (pattern_subst s p, term_substitution s' t)) eqs,
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
  let s' = shift_substitution s (pattern_fqvars_size p) in
  (pattern_subst s p, s')

and pattern_subst (s: substitution) (p: pattern) : pattern =
  match p with
    | PVar (n, te) -> PVar (n, term_substitution s te)
    | PAVar te -> PAVar (term_substitution s te)
    | PCste (symb, te) -> PCste (symb, term_substitution s te)
    | PAlias (n, p, te) -> PAlias (n, pattern_subst s p, term_substitution s te)
    | PApp (f, args, te) -> PApp (pattern_subst s f, 
				  List.map (fun (p, n) -> (pattern_subst s p, n)) args, 
				  term_substitution s te)
    | PType u -> PType u

and patterns_substitution (s: substitution) (p: pattern list) : (pattern list * substitution) =
  List.fold_left (fun (ps, s) p -> 
    let (p, s) = pattern_substitution s p in
    (ps @ [p], s)
  ) ([], s) p

(* aging a substitution: 
   shift the quantified variable index by delta
   delta > 0 -> consider the substitution on quantified terms
   delta < 0 -> consider the substitution on less quantified terms
*)

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
	let (p', level') = leveled_shift_pattern p level delta in
	(eqs @ [(p', leveled_shift_term t level' delta)], level')
      ) ([], level) eqs in
      Let (false, eqs', leveled_shift_term te level' delta)
      
    | Let (true, eqs, te) ->
      let sz = List.fold_left (fun acc hd -> acc + hd) 0 (List.map (fun hd -> pattern_fqvars_size (fst hd)) eqs) in 
      let level' = level + sz in
      Let (true,
	   List.map (fun (p, t) -> (leveled_shift_pattern' p level' delta, leveled_shift_term t level' delta)) eqs,
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
  List.fold_left (fun (ps, level) p ->
    let (p, level) = leveled_shift_pattern p level delta in
    (ps @ [p], level)
  ) ([], level) ps

and leveled_shift_pattern (p: pattern) (level: int) (delta: int) : pattern * int =
  (leveled_shift_pattern' p level delta,  level + (pattern_fqvars_size p))  

and leveled_shift_pattern' (p: pattern) (level: int) (delta: int) : pattern =
  match p with
    | PVar (n, te) -> PVar (n, leveled_shift_term te level delta)
    | PAVar te -> PAVar (leveled_shift_term te level delta)
    | PCste (symb, te) -> PCste (symb, leveled_shift_term te level delta)
    | PAlias (n, p, te) -> PAlias (n, leveled_shift_pattern' p level delta, leveled_shift_term te level delta)
    | PApp (f, args, te) -> PApp (leveled_shift_pattern' f level delta, 
				  List.map (fun (p, n) -> (leveled_shift_pattern' p level delta, n)) args, 
				  leveled_shift_term te level delta)
    | PType u -> PType u


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
  { frames = frames }
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

