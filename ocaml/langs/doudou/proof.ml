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
  some abstract datatype / functions needed
  in order to implement FOL
*)

type proof_pattern

type proof_subst

type hypothesises_iterator

exception NoPatternMatching

let match_proof_pattern (p: proof_pattern) (te: term) : proof_subst =
  raise Exit

let proof_pattern2term (p: proof_pattern) : term =
  raise Exit

let proof_pattern_subst (p: proof_pattern) (s: proof_subst) : proof_pattern =
  raise Exit

let make_iterator (hyps: hypothesises) (p: proof_pattern) : hypothesises_iterator =
  raise Exit

exception NoMoreHypothesis

let next_hypothesis (it: hypothesises_iterator) : (string * hypothesis) =
  raise Exit


type tactics = 
  (* just fail *) 
  | Fail      

  (* printout a message and continue *)
  | Msg of string * tactics
  (* printout the goal and continue *)
  | ShowGoal of tactics
      
  (* terminal tactic *)
  | Exact of proof_pattern
      
  (* partial apply of a term, executing the tactics on each subgoals *)
  | PartApply of proof_pattern * tactics
		   
  (* Interactive: asking for the user to enter a tactic *)
  | Interactive 

  (* try several tactics, rolling back after each fails, excpet the last one *)
  | Or of tactics list

  (* cases on the goal/hypothesises *)
  | Cases of (proof_pattern * (string * proof_pattern) list * tactics) list

  (* tactic name *)
  | TacticsName of string

  (* tactics call *)
  | Call of string * tactics list

  (* add an hypothesis *)
  | AddHyp of string * proof_pattern * proof_pattern * tactics

  (* introduce a quantification *)
  | Intro of string list * tactics




