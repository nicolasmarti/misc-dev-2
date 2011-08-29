open Parser
open Pprinter
open Doudou
open Printf
(*
  This is an attempt to have a facility for building proof s
*)

let debug = ref false


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

exception NoSuchHyp 

(* remove an hypothesis by name *)
let remove_hyp_by_name (hyps: hypothesises) (name: string) : hypothesises =
    try 
      let prefix = String.sub name 0 (String.index name '.') in    
      NameMap.add prefix (NameMap.remove name (NameMap.find prefix hyps)) hyps
    with
      | Not_found -> raise NoSuchHyp 


(* get an hypothesis by name *)
let get_hyp_by_name (hyps: hypothesises) (name: string) : hypothesis =
    try 
      let prefix = String.sub name 0 (String.index name '.') in
      NameMap.find name (NameMap.find prefix hyps)
    with
      | Not_found -> raise NoSuchHyp 

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
      mutable hyp_names: NameSet.t
    }

exception NoMoreHypothesis

(* returns the next hypothesis and update the iterator *)

let rec next_hypothesis (it: hypothesises_iterator) : (string * hypothesis) =
  try 
    let hyp_name, hyp = NameMap.choose it.next_hyp in
    it.next_hyp <- NameMap.remove hyp_name it.next_hyp;
    hyp_name, hyp
  with
    | Not_found -> 
      try (
	let hyps_name, hyps = NameMap.choose it.next_hyps in
	it.next_hyps <- NameMap.remove hyps_name it.next_hyps;
	it.next_hyp <- hyps;
	next_hypothesis it
      ) with
	| Not_found -> raise NoMoreHypothesis	       

(* iterator loop *)
let rec iterator_loop (it: hypothesises_iterator) (f: string * hypothesis -> 'a option) : 'a option =
  try 
    let res = ref None in  
    while !res = None do
      res := f (next_hypothesis it)
    done;
    !res
  with
    | NoMoreHypothesis -> None

let iterator_size (it: hypothesises_iterator) : int =
  NameMap.fold (fun k v acc -> acc + NameMap.cardinal v) it.next_hyps (NameMap.cardinal it.next_hyp)


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
  if !debug then printf "trying unification: %s Vs %s\n" (proof_pattern2string ctxt p) (term2string ctxt.ctxt te); flush Pervasives.stdout;
  (* for sake of optimization we catch all impossible cases before using term unification *)
  match term2category te, term2category (proof_pattern2term ctxt p) with
    | cat1, cat2 when cat2 <> "??" && cat1 <> cat2 -> 
      if !debug then printf "%s <> %s\n" cat1 cat2;
      raise NoPatternMatching
    (* finally here we do not know *)
    | _ ->

      try (
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
	    if !debug then printf "passed the typeinference\n";
	    unification_term_term ctxt.defs ctxt' te' te
	  with
	    | DoudouException err -> 
	      if !debug then printf "cannot pattern match %s and %s: %s\n" (proof_pattern2string ctxt p) (term2string !ctxt' te) (error2string err); flush Pervasives.stdout;
	      raise NoPatternMatching
	in
	(*
	  we just check that there is no free variables in the result
	*)
	if not (IndexSet.is_empty (fv_term te')) then (
	  if !debug then printf "still free vars in %s\n" (term2string ctxt.ctxt te); flush Pervasives.stdout;
	  raise NoPatternMatching;
	);
	(*
	  now we could recreate a substitution by replace the free variable of 
	  subst to their value, using the context substitution    
	*)
	let s = context2substitution !ctxt' in
	let subst = NameMap.map (term_substitution s) subst in
	(* and just return the result *)
	subst 
      ) with
	| DoudouException err ->
	  if !debug then printf "DoudouException: %s\n" (error2string err);
	  raise NoPatternMatching

	| NoPatternMatching -> raise NoPatternMatching

(* we transform a pattern into a term *)
and proof_pattern2term (ctxt: proof_context) (p: proof_pattern) : term =
  match p with
    | PPAVar -> AVar nopos
    | PPCste s -> Cste (s, nopos)
    | PPVar v -> TName (Name (String.concat "" ["?"; v]), nopos)
    | PPImpl (p1, p2) -> Impl ((Symbol ("_", Nofix), proof_pattern2term ctxt p1, Explicit, nopos), proof_pattern2term ctxt p2, nopos)
    | PPApp (p, args) -> App (proof_pattern2term ctxt p, List.map (fun (arg, n) -> proof_pattern2term ctxt arg, n) args, nopos)
    | PPProof s -> fst (get_hyp_by_name ctxt.hyps s)
    | PPType s -> snd (get_hyp_by_name ctxt.hyps s)
    | PPTerm te -> te

(* apply substitution into a pattern *)
and proof_pattern_subst (p: proof_pattern) (s: proof_subst) (h: hyp_subst) : proof_pattern =
  match p with
    | PPAVar | PPCste _ | PPTerm _ -> p
    | PPType n -> (try PPType (NameMap.find n h) with | Not_found -> p)
    | PPProof n -> (try PPProof (NameMap.find n h) with | Not_found -> p)
    | PPVar v -> (
      try
	PPTerm (NameMap.find v s)
      with
	| Not_found -> p
    )
    | PPApp (p, args) -> PPApp (proof_pattern_subst p s h, List.map (fun (arg, n) -> proof_pattern_subst arg s h, n) args)
    | PPImpl (p1, p2) -> PPImpl (proof_pattern_subst p1 s h, proof_pattern_subst p2 s h)
and proof_pattern2string (ctxt: proof_context) (p: proof_pattern) : string = 
  let te = proof_pattern2term ctxt p in
  term2string ctxt.ctxt te
and proof_pattern2token (ctxt: proof_context) (p: proof_pattern) : token = 
  let te = proof_pattern2term ctxt p in
  term2token ctxt.ctxt te Alone



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
      | cat -> (try { next_hyps = NameMap.empty; next_hyp = NameMap.find cat ctxt.hyps } with | Not_found -> { next_hyps = NameMap.empty; next_hyp = NameMap.empty })
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

  (* add an hypothesis *)
  | AddHyp of string * proof_pattern * proof_pattern * tactic

  (* remove an hypothesis *)
  | DelHyp of string * tactic

  (* introduce a quantification *)
  | Intro of string list * tactic

(******************************************)
(*  pretty printer and parser for tactics *)
(******************************************)

let rec tactic2token (ctxt: proof_context) (t: tactic) : token =
  match t with
    | Fail -> Verbatim "Fail"
    | Interactive -> Verbatim "Interactive"
    | Intro (names, t) -> Box [Verbatim "Intro"; Space 1; Box (intercalate (Space 1) (List.map (fun n -> Verbatim n) names)); Verbatim ";"; Space 1; tactic2token ctxt t]
    | Exact p ->
      Box [Verbatim "Exact"; Space 1; proof_pattern2token ctxt p]

let tactic2string (ctxt: proof_context) (t: tactic) : string =
  let token = tactic2token ctxt t in
  let box = token2box token 100 2 in
  box2string box

let create_opparser_proof_pattern (ctxt: proof_context) (primary: proof_pattern parsingrule) : proof_pattern opparser =
  let res = { primary = primary;
	      prefixes = Hashtbl.create (List.length ctxt.defs.hist);
	      infixes = Hashtbl.create (List.length ctxt.defs.hist);
	      postfixes = Hashtbl.create (List.length ctxt.defs.hist);
	      reserved = parse_reserved;
	    } in
  let _ = List.map (fun s -> 
    match s with
      | Name _ -> ()
      | Symbol (n, Nofix) -> ()
      | Symbol (n, Prefix i) -> Hashtbl.add res.prefixes n (i, fun pos te -> PPApp (PPCste s, [te, Explicit]))
      | Symbol (n, Infix (i, a)) -> Hashtbl.add res.infixes n (i, a, fun pos te1 te2 -> PPApp (PPCste s, [te1, Explicit; te2, Explicit]))
      | Symbol (n, Postfix i) -> Hashtbl.add res.postfixes n (i, fun pos te -> PPApp (PPCste s, [te, Explicit]))
  ) ctxt.defs.hist in
  res


let rec proof_pattern_parser (ctxt: proof_context) (pb: parserbuffer) : proof_pattern = begin
  let myp = create_opparser_proof_pattern ctxt (parse_proof_pattern_lvl1 ctxt) in
  opparse myp
end pb

and parse_proof_pattern_lvl1 (ctxt: proof_context) (pb: parserbuffer) : proof_pattern = begin
  fun pb -> 
    (* first we parse the application head *)
    let head = parse_proof_pattern_lvl2 ctxt pb in    
    let () = whitespaces pb in
    (* then we parse the arguments *)
    let args = separatedBy (
      fun pb ->
      parse_proof_pattern_arguments ctxt pb
    ) whitespaces pb in
    match args with
      | [] -> head
      | _ -> 
	PPApp (head, args)
end pb

and parse_proof_pattern_arguments  (ctxt: proof_context) (pb: parserbuffer) : proof_pattern * nature = begin
  (fun pb -> 
    let te = bracket (parse_proof_pattern_lvl2 ctxt) pb in
    (te, Implicit)
  )
  <|> (fun pb -> 
    let te = parse_proof_pattern_lvl2 ctxt pb in
    (te, Explicit)
  )
end pb

and parse_proof_pattern_lvl2 (ctxt: proof_context) (pb: parserbuffer) : proof_pattern = begin
  tryrule (fun pb -> 
    let () = whitespaces pb in
    let (), pos = with_pos (word "Type") pb in
    let () = whitespaces pb in
    PPTerm (Type pos)
  ) 
  <|> tryrule (fun pb ->
    let () =  whitespaces pb in
    let () = parse_avar pb in
    let () =  whitespaces pb in
    PPAVar
  ) 
  <|> tryrule (fun pb -> 
    let () =  whitespaces pb in
    let s = parse_symbol_name ctxt.defs pb in
    let () =  whitespaces pb in    
    PPCste s
  )
  <|> tryrule (fun pb -> 
    let () =  whitespaces pb in
    let () = word "proof(" pb in
    let n = name_parser pb in
    let () = word ")" pb in
    let () =  whitespaces pb in    
    PPProof n
  )
  <|> tryrule (fun pb -> 
    let () =  whitespaces pb in
    let () = word "type(" pb in
    let n = name_parser pb in
    let () = word ")" pb in
    let () =  whitespaces pb in    
    PPProof n
  )
  <|> (paren (proof_pattern_parser ctxt))
end pb

and tactic_parser (ctxt: proof_context) (pb: parserbuffer) : tactic = begin
  tryrule (fun pb ->
    let () = whitespaces pb in
    let () = word "Fail" pb in
    let () = whitespaces pb in
    Fail
  )
  <|> tryrule (fun pb ->
    let () = whitespaces pb in
    let () = word "Interactive" pb in
    let () = whitespaces pb in
    Interactive
  )
  <|> tryrule (fun pb ->
    let () = whitespaces pb in
    let () = word "Intro" pb in
    let () = whitespaces pb in
    let names = many (fun pb ->
      let () = whitespaces pb in
      let n = name_parser pb in
      let () = whitespaces pb in
      n
    ) pb in
    let () = whitespaces pb in
    match (
      mayberule (fun pb ->
	let () = word ";" pb in
	let () = whitespaces pb in
	tactic_parser ctxt pb 
    ) pb) with
      | None -> Intro (names, Interactive)
      | Some t -> Intro (names, t)
  )
  <|> tryrule (fun pb ->
    let () = whitespaces pb in
    let () = word "Exact" pb in
    let () = whitespaces pb in
    let pp = proof_pattern_parser ctxt pb in
    Exact pp
  )
end pb

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
    | AddHyp (n, prf, lemma, t) -> AddHyp ((try NameMap.find n h with | Not_found -> n), proof_pattern_subst prf s h, proof_pattern_subst lemma s h, tactic_subst t s h)
    | DelHyp (n, t) -> DelHyp ((try NameMap.find n h with | Not_found -> n), tactic_subst t s h) 
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
  a map from string to tactics 
  used for keeping tactics definitions, and for tactics arguments
*)
(*
  first we will have a "global" dict of tactics
*)

open Hashtbl

type tactics_dict = (string, tactic) Hashtbl.t

let global_tactics : tactics_dict = Hashtbl.create 50

let rec tactic_semantics (t: tactic) (ctxt: proof_context) (goal: term) : term =
  (*
  printf "tactic: %s\n" (tactic2string t); flush Pervasives.stdout;
  printf "on goal: %s\n" (term2string ctxt.ctxt goal); flush Pervasives.stdout;
  *)
  (*printf "%s\n\n" (proof_state2string ctxt goal); *)
  match t with
    | Fail -> raise CannotSolveGoal

    | Msg (s, t) ->
      printf "%s\n" s; flush Pervasives.stdout;
      tactic_semantics t ctxt goal

    | ShowGoal t ->
      printf "%s\n\n" (proof_state2string ctxt goal); flush Pervasives.stdout;
      tactic_semantics t ctxt goal

    | Exact p -> (
      let prf = proof_pattern2term ctxt p in      
      try 
	let prf, _ = typecheck ctxt.defs (ref ctxt.ctxt) prf goal in
	prf
      with
	| DoudouException err ->
	  printf "fail in exact: %s\n" (error2string err);
	  raise CannotSolveGoal
	| CannotSolveGoal -> raise CannotSolveGoal
    )

    | PartApply (prf, t) -> 
      (* first we rebuild the term *)
      let prf = proof_pattern2term ctxt prf in
      (* then we typeinfer the term *)
      let ctxt' = ref ctxt.ctxt in
      let prf, ty = typeinfer ctxt.defs ctxt' prf in
      (*printf "infered apply: %s :: %s\n" (term2string !ctxt' prf) (term2string !ctxt' ty);*)
      let fvs, prf' = complete_explicit_arguments ctxt' prf ty in
      (*printf "completed term: %s\n" (term2string !ctxt' prf');*)
      (* we typecheck against the goal to infer the free variables type *)
      let prf', ty = typecheck ctxt.defs ctxt' prf' goal in
      (*printf "infered apply: %s :: %s\n" (term2string !ctxt' prf') (term2string !ctxt' ty);*)
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

    | Interactive -> (
      printf "%s\n\n> " (proof_state2string ctxt goal); flush Pervasives.stdout;
      let lines = line_stream_of_channel stdin in
      let pb = build_parserbuffer lines in
      let t = 
	try 
	  tactic_parser ctxt pb 
	with
	  | NoMatch -> 
	    printf "parsing error: '%s'\n%s\n" (Buffer.contents pb.bufferstr) (errors2string pb);
	    Interactive
      in
      if t = Fail then raise CannotSolveGoal else
	try
	  printf "entered tactic: %s\n" (tactic2string ctxt t);
	  tactic_semantics t ctxt goal
	with
	  | DoudouException err ->
	    printf "error:\n%s\n" (error2string err);
	    tactic_semantics Interactive ctxt goal
	  | NoMatch -> 
	    printf "parsing error: '%s'\n%s\n" (Buffer.contents pb.bufferstr) (errors2string pb);
	    tactic_semantics Interactive ctxt goal
	  | CannotSolveGoal ->
	    printf "the tactic does not solve the goal\n";
	    tactic_semantics Interactive ctxt goal
    )
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

    | TacticName s -> (
      let t = (
      try 
	Hashtbl.find global_tactics s
      with 
	| Not_found -> 
	  printf "tactic '%s'\n is unknown\n" s; 
	  Hashtbl.iter (fun key value -> 
	    printf "Tactic '%s'\n" key
	  )  global_tactics;
	  raise CannotSolveGoal
      ) in 
      tactic_semantics t ctxt goal
    )

    | AddHyp (s, prf, lemma, t) -> (
	if !debug then printf "create new hyp %s :: %s\n" (proof_pattern2string ctxt prf) (proof_pattern2string ctxt lemma);
	(* build both terms *)
	let prf = proof_pattern2term ctxt prf in
	let lemma = proof_pattern2term ctxt lemma in
	(* typecheck them *)
	let ctxt' = ref ctxt.ctxt in
	let lemma, _ = typecheck ctxt.defs ctxt' lemma (Type nopos) in
	let prf, lemma = typecheck ctxt.defs ctxt' prf lemma in
	let prf = reduction ctxt.defs ctxt' unification_strat prf in
	let lemma = reduction ctxt.defs ctxt' unification_strat lemma in
	if !debug then printf "AddHyp: (%s, %s)\n" (term2string !ctxt' prf) (term2string !ctxt' lemma);
	(* just check that there is no free var *)
	if not (IndexSet.is_empty (fv_term lemma) && IndexSet.is_empty (fv_term prf)) then raise CannotSolveGoal;
	(* add the hypothesis *)
	let hyps = input_hypothesis (prf, lemma) ~name:s ctxt.hyps in
	(* continue *)
	tactic_semantics t {ctxt with hyps = hyps} goal
    )

    | DelHyp (s, t) ->
      (*printf "del hyp %s\n" s;*)
      tactic_semantics t {ctxt with hyps = remove_hyp_by_name ctxt.hyps s} goal

    | Cases cases -> 
      if !debug then printf "Tactic cases with %d patterns\n" (List.length cases);
      (* we traverse all the goals until we get a proof of we return an error *)
      let res = fold_stop (fun () (goal_p, hyps_ps, t) ->
	if !debug then printf "trying one case\n";
	try 
	  if !debug then printf "trying to match goal pattern: %s\n" (proof_pattern2string ctxt goal_p);
	  if !debug then printf "against goal: %s\n" (term2string ctxt.ctxt goal);
	  (* first we need to pattern match the gaol *)
	 (* printf "pattern matching goal: %s Vs %s ... " (proof_pattern2string ctxt goal_p) (term2string ctxt.ctxt goal); flush Pervasives.stdout;*)
	  let subst = try (
	    let subst = match_proof_pattern ctxt goal_p goal in
	    (*printf "done ok\n"; flush Pervasives.stdout;*)
	    subst
	  ) with | e -> (*printf "done nok\n"; flush Pervasives.stdout; *)raise e in
	  if !debug then printf "goal matched!\n";
	  (* then we try to matches the hypothesises *)
	  Right (hyps_matching ctxt subst NameMap.empty hyps_ps [] t goal)
	with
	  (* the goal does not match => go to another case *)
	  | NoPatternMatching -> if !debug then printf "Case: no pattern-matching with goal/hyps\n"; Left ()
	  | CannotSolveGoal -> if !debug then printf "pattern matched goal / hyps but further tactics failed\n"; Left ()
	  | DoudouException err -> printf "%s\n" (error2string err); Left ()
      ) () cases in
      match res with
	| Left () -> raise CannotSolveGoal
	| Right prf -> prf

(* we add the used_hyp, a list of used hyp, such that they are not pattern match in further hyps patterns *)
and hyps_matching (ctxt: proof_context) (s: proof_subst) (h: hyp_subst) (hyps_ps: (string * proof_pattern) list) (used_hyp: string list) (action: tactic) (goal: term) : term =
  match hyps_ps with
    (* all hypothesis patterns have been matched, we need to try apply the tactics *)
    | [] -> 
      if !debug then printf "run the case tactics!\n";
      tactic_semantics (tactic_subst action s h) ctxt goal

    (* else we need to try matching the next pattern *)
    | (n, p)::tl ->
      try (
	(* we first apply the substitutions to the pattern *)
	let p = proof_pattern_subst p s h in
	if !debug then printf "trying to match hyp pattern: %s :: %s\n" n (proof_pattern2string ctxt p);
	(* we build an iterator for this pattern *)
	let it = make_iterator ctxt p in
	(*printf "iterator_size := %d\n" (iterator_size it);*)
	(* we try all possibilities until there is none *)
	let res = iterator_loop it (fun (name, (prf, lemma)) ->
	  if !debug then printf "aginst hyp pattern: %s :: %s\n" name (term2string ctxt.ctxt lemma);
	  (* we make sure that the hypothesis is not already used *)
	  if List.mem name used_hyp then None else
	  try 
	    (* we try to match the lemma and the pattern *)
	    let subst' = match_proof_pattern ctxt p lemma in
	    if !debug then printf "pattern matching hyp: %s Vs %s\n" (proof_pattern2string ctxt p) (term2string ctxt.ctxt lemma); flush Pervasives.stdout;
	    (* we update the substitution and try further *)
	    let s = NameMap.merge (fun k v1 v2 ->
	      match v1, v2 with
		| Some v1, None -> Some v1
		| None, Some v2 -> Some v2
		| _ -> raise (Failure "cannot merge the substitutions")
	    ) subst' s in
	    let h = NameMap.add n name h in
	    (* trying further *)
	    Some (hyps_matching ctxt s h tl (name::used_hyp) action goal)
	  with
	    (* no match for the hypothesis, try another one *)
	    | NoPatternMatching -> None
            (* the goal cannot be solved, try another hypothesis *)
	    | CannotSolveGoal -> None
	    | NoSuchHyp -> None
	) in
	match res with
	  | None -> raise CannotSolveGoal
	  | Some prf -> prf
      ) 	    
      with
	| NoPatternMatching -> raise NoPatternMatching
	| CannotSolveGoal -> raise CannotSolveGoal
