open Parser
open Pprinter
open Doudou
open Printf
(*
  This is an attempt to have a facility for building proof s
*)

(*
  first we have the hypothesis 
  of the form prf * lemma 
  all terms type under the same context ctxt/defs such that
  ctxt |- prf :: lemma :: Type

  It means basically that the proof/type of hypothesis does not depends on other hypothesis
*)
type hypothesis = term * term

(*
  the hypothesis are stored by their category: a string representing their types
  see the following function for the mapping
*)
let term2category (te: term) : string =
  match te with
    | Type _ -> "Type"
    | Cste (s, _) | App (Cste (s, _), _, _) -> symbol2string s
    | TVar _ -> "Var"
    | Impl _ -> "(->)"
    (* other term should not be hypothesis (that we consider in normal formal form (== beta reduced)) *)
    | _ -> "??"

module NameMap = Map.Make(
  struct
    type t = string
    let compare x y = compare x y
  end
);;

(* the first level represent category, the second names of the hypothesis *)
type hypothesises = (hypothesis NameMap.t) NameMap.t

(*
  few helper functions on hypothesis
*)

(* shifting of hypothesises, all hypothesises which cannot be shifted (due to negative shifting) *)
let shift_hypothesises (hyps: hypothesises) (level: int) =
  NameMap.fold (fun category hyps acc ->
    NameMap.add category (
      NameMap.fold (fun name (prf, lemma) acc ->
	try 
	  NameMap.add name (shift_term prf level, shift_term lemma level) acc
	with
	  | DoudouException (Unshiftable_term _) -> acc
      ) hyps NameMap.empty
    ) acc
  ) hyps NameMap.empty

(* a function that check that all hypothesis are well typed *)
let check_hypothesis (defs: defs) (ctxt: context) (hyps: hypothesises) : unit =
  NameMap.iter (fun category hyps -> 
    NameMap.iter (fun name (prf, lemma) -> 
      ignore(typecheck defs (ref ctxt) lemma (Type nopos));
      ignore(typecheck defs (ref ctxt) prf lemma)
    ) hyps
  ) hyps

(* hypothesis2 token *)
let hypothesises2token (ctxt: context) (hyps: hypothesises) : token =
  Box (
    NameMap.fold (fun category hyps acc ->
      acc @ (NameMap.fold (fun key (prf, lemma) acc ->
	acc @ [Box [Verbatim key; Space 1; Verbatim "::"; Space 1; term2token ctxt lemma Alone]; Newline]
      ) hyps [])
    ) hyps []
  )

(* input an hypothesis in a proof_context *)
let input_hypothesis (hyp: hypothesis) ?(name: string = "H") (hyps: hypothesises) : hypothesises =
  (* grab the proof and the lemma *)
  let prf, lemma = hyp in
  (* find the category (create an empty map of hypothesises if it does not exists) *)
  let category = term2category lemma in
  let category_hyps = try NameMap.find category hyps with | Not_found -> NameMap.empty in
  (* grab the names of this category hypothesis, and generate a fresh name from the given one *)
  let category_hyps_names = NameMap.fold (fun k _ acc -> NameSet.add k acc) category_hyps NameSet.empty in
  let name = String.concat "." [category; name] in
  let name = fresh_name ~basename:name category_hyps_names in
  (* and finally update the map of hypothesis *)
  (* please note that we do not check for duplicate *)
  let category_hyps = NameMap.add name hyp category_hyps in
  NameMap.add category category_hyps hyps

(* remove an hypothesis by name *)
let remove_hyp_by_name (hyps: hypothesises) (name: string) : hypothesises =
    let prefix = String.sub name 0 (String.index name '.') in
    NameMap.add prefix (NameMap.remove name (NameMap.find prefix hyps)) hyps


(* get an hypothesis by name *)
let get_hyp_by_name (hyps: hypothesises) (name: string) : hypothesis =
    let prefix = String.sub name 0 (String.index name '.') in
    NameMap.find name (NameMap.find prefix hyps)

(*
  this is the proof context

  defs: the global definitions under which all Cste types
  ctxt: the global context under which all Variables types
  hyps: the current set of hypothesis (valid under defs, ctxt)

*)

type proof_context = {
  defs: defs;
  ctxt: context;
  hyps: hypothesises;
}

(*
  pretty print of a proof_context
*)
let proof_context2token (ctxt: proof_context) : token =
  Bar (true,
    Bar (true, Verbatim " ",
	 Bar 
	   (false,
	    Bar (true, 
		 Box [Verbatim "   DEFINITIONS:";
		      Newline; 
		      Verbatim "-----------------";
		      Newline; 
		      defs2token ctxt.defs], 
		 Box [Verbatim "   CONTEXT:";
			Newline; 
			Verbatim "--------------";
			Newline; 
			context2token ctxt.ctxt]),
	    Box [Verbatim "   HYPOTHESIS:"; 
		 Newline; 
		 Verbatim "-----------------"; 
		 Newline; 
		 hypothesises2token ctxt.ctxt ctxt.hyps])	   
    ), Verbatim " ")

let proof_context2string (ctxt: proof_context) : string =
  let token = proof_context2token ctxt in
  let box = token2box token 100 2 in
  box2string box

let proof_state2token (ctxt: proof_context) (goal: term) : token =
  Bar (true,
    Bar (true, Verbatim " ",
	 Bar 
	   (false,
	    Bar (true, 
		 Box [Verbatim "   DEFINITIONS:";
		      Newline; 
		      Verbatim "-----------------";
		      Newline; 
		      defs2token ctxt.defs], 
		 Box [Verbatim "   CONTEXT:";
			Newline; 
			Verbatim "--------------";
			Newline; 
			context2token ctxt.ctxt]),
	    Box [Verbatim "   HYPOTHESIS:"; 
		 Newline; 
		 Verbatim "-----------------"; 
		 Newline; 
		 hypothesises2token ctxt.ctxt ctxt.hyps])	   
    ), Box [Verbatim "goal:"; Newline; ISpace 4; term2token ctxt.ctxt goal Alone])

let proof_state2string (ctxt: proof_context) (goal: term) : string =
  let token = proof_state2token ctxt goal in
  let box = token2box token 100 2 in
  box2string box

(*
  the empty proof_context
*)

let empty_proof_context (defs: defs) = {
  defs = defs;
  ctxt = empty_context;
  hyps = NameMap.empty;
}

(*
  a flag that check whenever needed that a proof_context and the goals are valid
*)

let force_check = ref true

(*
  an exception when a goal cannot be solved
*)
exception CannotSolveGoal

(*
  checking a proof context and goals
*)
let check_proof_context (ctxt: proof_context) (goals: (term * term) list) : unit =
  ignore(check_hypothesis ctxt.defs ctxt.ctxt ctxt.hyps);
  ignore(List.iter (fun (prf, goal) -> 
    ignore(typecheck ctxt.defs (ref ctxt.ctxt) goal (Type nopos));
    ignore(typecheck ctxt.defs (ref ctxt.ctxt) prf goal);
  ) goals)

(*
  push/pop a quantification in a proof_context
*)
let push_quantification (ctxt: proof_context) (q : symbol * term * nature * pos) : proof_context =
  (* we compute the new context *)
  let ctxt' = let ctxt = ref ctxt.ctxt in push_quantification q ctxt; !ctxt in
  (* we compute the new hypothesises *)
  let hyps' = shift_hypothesises ctxt.hyps 1 in
  {ctxt with ctxt = ctxt'; hyps = hyps'}

let pop_quantification (ctxt: proof_context) (prf: term) : proof_context * (symbol * term * nature * pos) * term =
  let ctxt', q, prf = 
    let ctxt = ref ctxt.ctxt in 
    let q, [prf] = pop_quantification ctxt [prf] in 
    !ctxt, q, prf
  in
  let hyps' = shift_hypothesises ctxt.hyps (-1) in
  {ctxt with ctxt = ctxt'; hyps = hyps'}, q, prf

(*
  pattern matching for the hypothesis / goal
*)

(* the patterns used to match lemma and build proof *)
type proof_pattern = PPAVar
		     | PPCste of symbol
		     | PPVar of string
		     | PPImpl of proof_pattern * proof_pattern (* no dependant type here, only Explicit *)
		     | PPApp of proof_pattern * (proof_pattern * nature) list
		     | PPProof of string
		     | PPType of string
		     | PPTerm of term

(* substitution of pattern variable to term *)
type proof_subst = term NameMap.t

(* substitution of hypothesis name  *)
type hyp_subst = string NameMap.t

(* hypothesis iterator: used in order to traverse hypothesis in pattern matching 
   with side effect
*)
type hypothesises_iterator = 
    { mutable next_hyps : hypothesises;
      mutable next_hyp : hypothesis NameMap.t;
    }

exception NoMoreHypothesis

(* returns the next hypothesis and update the iterator *)

let rec next_hypothesis (it: hypothesises_iterator) : (string * hypothesis) =
  try 
    let hyp_name, hyp = NameMap.choose it.next_hyp in
    it.next_hyp <- NameMap.remove hyp_name it.next_hyp;
    hyp_name, hyp
  with
    | Not_found -> let hyps_name, hyps = NameMap.choose it.next_hyps in
		   it.next_hyps <- NameMap.remove hyps_name it.next_hyps;
		   it.next_hyp <- hyps;
		   next_hypothesis it
    

(* grab all the pattern variables of a pattern *)
let rec proof_pattern_variable (p: proof_pattern) : NameSet.t =
  match p with
    | PPVar v -> NameSet.singleton v
    | PPImpl (hyp, ccl) -> NameSet.union (proof_pattern_variable hyp) (proof_pattern_variable ccl)
    | PPApp (f, args) ->  List.fold_left (fun acc (arg, _) -> NameSet.union (proof_pattern_variable arg) acc) (proof_pattern_variable f) args
    | _ -> NameSet.empty

exception NoPatternMatching

(* we match proof_pattern with a term *)
let rec match_proof_pattern (ctxt: proof_context) (p: proof_pattern) (te: term) : proof_subst =
  (* we make a copy of the context *)
  let ctxt' = ref (ctxt.ctxt) in
  (* then we grab all the pattern variables *)
  let vars = proof_pattern_variable p in
  (* we create a free variable for each vars 
     and create a substitution
  *)
  let subst = NameSet.fold (fun v acc ->
    let fvty = add_fvar ctxt' (Type nopos) in
    let fvte = add_fvar ctxt' (TVar (fvty, nopos)) in
    NameMap.add v (TVar (fvte, nopos)) acc
  ) vars NameMap.empty in
  (*
    we apply the substitution 
  *)
  let p' = proof_pattern_subst p subst NameMap.empty in
  (*
    we create a term with it
  *)
  let te' = proof_pattern2term ctxt p' in
  (*
    we typeinfer the term and then we unify with te 
  *)
  let te' = 
    try 
      let te', _ = typeinfer ctxt.defs ctxt' te' in
      unification_term_term ctxt.defs ctxt' te te'
    with
      | DoudouException _ -> raise NoPatternMatching
  in
  (*
    we just check that there is no free variables in the result
  *)
  if not (IndexSet.is_empty (fv_term te')) then raise NoPatternMatching;
  (*
    now we could recreate a substitution by replace the free variable of 
    subst to their value, using the context substitution    
  *)
  let s = context2substitution !ctxt' in
  let subst = NameMap.map (term_substitution s) subst in
  (* and just return the result *)
  subst 

(* we transform a pattern into a term *)
and proof_pattern2term (ctxt: proof_context) (p: proof_pattern) : term =
  match p with
    | PPAVar -> AVar nopos
    | PPCste s -> Cste (s, nopos)
    | PPVar _ -> AVar nopos
    | PPImpl (p1, p2) -> Impl ((Symbol ("_", Nofix), proof_pattern2term ctxt p1, Explicit, nopos), proof_pattern2term ctxt p2, nopos)
    | PPApp (p, args) -> App (proof_pattern2term ctxt p, List.map (fun (arg, n) -> proof_pattern2term ctxt arg, n) args, nopos)
    | PPProof s -> fst (get_hyp_by_name ctxt.hyps s)
    | PPType s -> snd (get_hyp_by_name ctxt.hyps s)
    | PPTerm te -> te

(* apply substitution into a pattern *)
and proof_pattern_subst (p: proof_pattern) (s: proof_subst) (h: hyp_subst) : proof_pattern =
  match p with
    | PPAVar | PPCste _ | PPTerm _ -> p
    | PPType n -> (try PPType (NameMap.find n h) with | _ -> p)
    | PPProof n -> (try PPProof (NameMap.find n h) with | _ -> p)
    | PPVar v -> (
      try
	PPTerm (NameMap.find v s)
      with
	| _ -> p
    )
    | PPApp (p, args) -> PPApp (proof_pattern_subst p s h, List.map (fun (arg, n) -> proof_pattern_subst arg s h, n) args)
    | PPImpl (p1, p2) -> PPImpl (proof_pattern_subst p1 s h, proof_pattern_subst p2 s h)

(* build an iterator over the hypothesises that might be matched with the pattern *)
let make_iterator (ctxt: proof_context) (p: proof_pattern) : hypothesises_iterator =
  (* first we create a term from the pattern *)
  let te = proof_pattern2term ctxt p in
  (* then we get the category of the term *)
  let category = term2category te in
  (* then we filter the hypothesises of interest depending on the category *)
  let iterator = 
    match category with
      (* general pattern -> we take everything *)
      | "??" -> { next_hyps = ctxt.hyps; next_hyp = NameMap.empty }
      (* for the rest we take the hypothesis of the same category *)
      | cat -> try { next_hyps = NameMap.empty; next_hyp = NameMap.find cat ctxt.hyps } with | _ -> raise NoPatternMatching
  in
  iterator

(*
  the tactic AST
*)

type tactic = 
  (* just fail *) 
  | Fail      

  (* printout a message and continue *)
  | Msg of string * tactic

  (* printout the goal and continue *)
  | ShowGoal of tactic
      
  (* terminal tactic *)
  | Exact of proof_pattern
      
  (* partial apply of a term, executing the tactic on each subgoals *)
  | PartApply of proof_pattern * tactic
		   
  (* Interactive: asking for the user to enter a tactic *)
  | Interactive 

  (* try several tactic, rolling back after each fails, excpet the last one *)
  | Or of tactic list

  (* cases on the goal/hypothesises *)
  | Cases of (proof_pattern * (string * proof_pattern) list * tactic) list

  (* tactic name *)
  | TacticName of string

  (* tactic call *)
  | Call of string * tactic list

  (* add an hypothesis *)
  | AddHyp of string * proof_pattern * proof_pattern * tactic

  (* remove an hypothesis *)
  | DelHyp of string * tactic

  (* introduce a quantification *)
  | Intro of string list * tactic

(*
  we might need to apply a substitution to a tactic
  h is a substitution for hypothesis names
*)
let rec tactic_subst (t: tactic) (s: proof_subst) (h: hyp_subst) : tactic =
  match t with
    (* the cases where we need to propagate the substitution *)
    | Msg (m, t) -> Msg (m, tactic_subst t s h)
    | ShowGoal t -> ShowGoal (tactic_subst t s h)
    | Exact p -> Exact (proof_pattern_subst p s h)
    | PartApply (p, t) -> PartApply (proof_pattern_subst p s h, tactic_subst t s h)
    | Or ts -> Or (List.map (fun t -> tactic_subst t s h) ts)
    | Call (n, ts) -> Call (n, List.map (fun t -> tactic_subst t s h) ts)
    | AddHyp (n, prf, lemma, t) -> AddHyp (NameMap.find n h, proof_pattern_subst prf s h, proof_pattern_subst lemma s h, tactic_subst t s h)
    | DelHyp (n, t) -> DelHyp (NameMap.find n h, tactic_subst t s h) 
    | Intro (l, t) -> Intro (l, 
			     (* from the hyp subst we remove the one comming from the intro *)
			     tactic_subst t s (List.fold_left (fun acc hd -> NameMap.remove hd acc) h l)
    )
    | Cases cases ->
      Cases (List.map (fun (gp, hp, t) ->
	(* we remove the patterns vars and hyp names from s and h*)
	let pattern_vars = List.fold_left (fun acc (_, hd) -> NameSet.union acc (proof_pattern_variable hd)) (proof_pattern_variable gp) hp in
	let s = NameSet.fold (fun k acc -> NameMap.remove k acc) pattern_vars s in
	let names = List.map fst hp in
	let h = List.fold_left (fun acc hd -> NameMap.remove hd acc) h names in
	gp, hp, tactic_subst t s h
      ) cases)
    | Fail | Interactive | TacticName _ -> t

(*
  a map from string to tactics 
  used for keeping tactics definitions, and for tactics arguments
*)
open Hashtbl

type tactics_dict = (string, name list * tactic) Hashtbl.t

(*
  valuation of an tactic

  given a proof_context and a goal, it returns a proof
*)

(* this function apply to a term a free variable for each of its remaining arguments *)
let rec complete_explicit_arguments (ctxt: context ref) (te: term) (ty: term) : index list * term =
  match ty with
    | Impl ((_, _, nature, _), ty, _) ->
      let fvty = add_fvar ctxt (Type nopos) in
      let fvte = add_fvar ctxt (TVar (fvty, nopos)) in
      let fvs, te = complete_explicit_arguments ctxt (App (te, [TVar (fvte, nopos), nature], nopos)) ty in
      fvte::fvs, te
    | _ -> [], te  

(*
  first we will have a "global" dict of tactics
*)

let global_tactics : tactics_dict = Hashtbl.create 50

let rec tactic_semantics (t: tactic) (ctxt: proof_context) (goal: term) : term =
  match t with
    | Fail -> raise CannotSolveGoal

    | Msg (s, t) ->
      printf "%s\n" s;
      tactic_semantics t ctxt goal

    | ShowGoal t ->
      printf "%s\n\n" (proof_state2string ctxt goal); 
      tactic_semantics t ctxt goal

    | Exact p -> (
      let prf = proof_pattern2term ctxt p in      
      try 
	let prf, _ = typecheck ctxt.defs (ref ctxt.ctxt) prf goal in
	prf
      with
	| DoudouException err ->
	  printf "%s\n" (error2string err);
	  raise CannotSolveGoal
	| _ -> raise CannotSolveGoal
    )

    | PartApply (prf, t) -> 
      (* first we rebuild the term *)
      let prf = proof_pattern2term ctxt prf in
      (* then we typeinfer the term *)
      let ctxt' = ref ctxt.ctxt in
      let prf, ty = typeinfer ctxt.defs ctxt' prf in
      printf "infered apply: %s :: %s\n" (term2string !ctxt' prf) (term2string !ctxt' ty);
      let fvs, prf' = complete_explicit_arguments ctxt' prf ty in
      printf "completed term: %s\n" (term2string !ctxt' prf');
      (* we typecheck against the goal to infer the free variables type *)
      let prf', _ = typecheck ctxt.defs ctxt' prf' goal in
      (* then we traverse the free variables in order to solve them *)
      let _ = List.fold_left (fun () hd ->
	(* first look if the value of the fvar is itself *)
	match fvar_value !ctxt' hd with
	  (* yes, we need to sovle this subgoal *)
	  | TVar (hd, _) -> 
	    let goal = fvar_type !ctxt' hd in
	    (* call the continuation *)
	    let prf = tactic_semantics t ctxt goal in
	    (* apply the substitution to the context *)
	    let s = IndexMap.singleton hd prf in
	    ctxt' := context_substitution s (!ctxt')
	  (* no: we do not need to look at it *)
	  | _ -> ()
      ) () fvs in
      (* here we should have every free variables with proper value in ctxt', we just need to substitute in prf' *)
      let prf = term_substitution (context2substitution !ctxt') prf' in
      (* just verify that there is no free variable *)
      if not (IndexSet.is_empty (fv_term prf)) then raise CannotSolveGoal;
      prf

    | Interactive -> 
      raise (Failure "tactic Interactive not yet implemented")

    | Or ts -> (
      (* we just try all the tactics until one returns, else we raise CannotSolveGoal *)
      let res = fold_stop (fun () t ->
	try 
	  Right (tactic_semantics t ctxt goal)
	with
	  | CannotSolveGoal -> Left ()
      ) () ts in
      match res with
	| Left () -> raise CannotSolveGoal
	| Right prf -> prf
    )

    (******** DUP !! *******)

    | Intro ([], t) -> (
      match goal with
	(* an implication, we can do a introduction *)
	| Impl ((s, ty, _, _) as q, body, pos) ->
	  (* quantifying the Impl *)
	  let ctxt = push_quantification ctxt q in
	  (* input a new hypothesis for it *)
	  let hyps = input_hypothesis (TVar (0, nopos), shift_term ty 1) ctxt.hyps in
	  (* try to solve the goal *)
	  let prf = tactic_semantics t { ctxt with hyps = hyps }  body in
	  (* do a check *)
	  if !force_check then check_proof_context ctxt [prf, body];
	  (* pop the quantification *)
	  let ctxt, q, prf = pop_quantification ctxt prf in
	  (* rebuilt the proof *)
	  let prf = Lambda (q, prf, nopos) in
	  (* do a check *)
	  if !force_check then check_proof_context ctxt [prf, goal];
	  (* return the result *)
	  prf

	(* not an implication, cannot introduce  *)
	| _ -> raise CannotSolveGoal
    )

    | Intro (hd::[], t) -> (
      match goal with
	(* an implication, we can do a introduction *)
	| Impl ((s, ty, _, _) as q, body, pos) ->
	  (* quantifying the Impl *)
	  let ctxt = push_quantification ctxt q in
	  (* input a new hypothesis for it *)
	  let hyps = input_hypothesis (TVar (0, nopos), shift_term ty 1) ~name:hd ctxt.hyps in
	  (* try to solve the goal *)
	  let prf = tactic_semantics t { ctxt with hyps = hyps }  body in
	  (* do a check *)
	  if !force_check then check_proof_context ctxt [prf, body];
	  (* pop the quantification *)
	  let ctxt, q, prf = pop_quantification ctxt prf in
	  (* rebuilt the proof *)
	  let prf = Lambda (q, prf, nopos) in
	  (* do a check *)
	  if !force_check then check_proof_context ctxt [prf, goal];
	  (* return the result *)
	  prf

	(* not an implication, cannot introduce  *)
	| _ -> raise CannotSolveGoal
    )

    | Intro (hd::tl, t) -> (
      match goal with
	(* an implication, we can do a introduction *)
	| Impl ((s, ty, _, _) as q, body, pos) ->
	  (* quantifying the Impl *)
	  let ctxt = push_quantification ctxt q in
	  (* input a new hypothesis for it *)
	  let hyps = input_hypothesis (TVar (0, nopos), shift_term ty 1) ~name:hd ctxt.hyps in
	  (* try to solve the goal *)
	  let prf = tactic_semantics (Intro (tl, t)) { ctxt with hyps = hyps }  body in
	  (* do a check *)
	  if !force_check then check_proof_context ctxt [prf, body];
	  (* pop the quantification *)
	  let ctxt, q, prf = pop_quantification ctxt prf in
	  (* rebuilt the proof *)
	  let prf = Lambda (q, prf, nopos) in
	  (* do a check *)
	  if !force_check then check_proof_context ctxt [prf, goal];
	  (* return the result *)
	  prf

	(* not an implication, cannot introduce  *)
	| _ -> raise CannotSolveGoal
    )

    (*************************)

    | Call (t, ts) -> (
      (* grab the tactics and its arguments *)
      let (argsname, t) = Hashtbl.find global_tactics t in
      (* push in the global dict *)
      let _ = List.map (fun (name, t) -> Hashtbl.add global_tactics name ([], t)) (List.combine argsname ts) in
      (* execute the tactics *)
      let res = 
	try 
	  Some (tactic_semantics t ctxt goal)
	with
	  | _ -> None
      in
      (* pop from the global dict *)
      let _ = List.map (fun name -> Hashtbl.remove global_tactics name) argsname in
      match res with
	| None -> raise CannotSolveGoal
	| Some prf -> prf
    )

    | TacticName s ->
      tactic_semantics (snd (Hashtbl.find global_tactics s)) ctxt goal

    | AddHyp (s, prf, lemma, t) ->
      (* build both terms *)
      let prf = proof_pattern2term ctxt prf in
      let lemma = proof_pattern2term ctxt lemma in
      (* typecheck them *)
      let ctxt' = ref ctxt.ctxt in
      let lemma, _ = typecheck ctxt.defs ctxt' lemma (Type nopos) in
      let prf, lemma = typecheck ctxt.defs ctxt' prf lemma in
      (* just check that there is no free var *)
      if not (IndexSet.is_empty (fv_term lemma) && IndexSet.is_empty (fv_term prf)) then raise CannotSolveGoal;
      (* add the hypothesis *)
      let hyps = input_hypothesis (prf, lemma) ctxt.hyps in
      (* continue *)
      tactic_semantics t {ctxt with hyps = hyps} goal

    | DelHyp (s, t) ->
      tactic_semantics t {ctxt with hyps = remove_hyp_by_name ctxt.hyps s} goal

    | _ -> raise (Failure "tactic not yet implemented")

      

