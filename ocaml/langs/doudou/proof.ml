open Doudou
open Parser
open Pprinter
(*
  This is an attempt to have a facility for step by step proof 
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
  for now we just store them into a map from name to hypothesis
*)

module NameMap = Map.Make(
  struct
    type t = string
    let compare x y = compare x y
  end
);;

type hypothesises = hypothesis NameMap.t

(*
  few helper functions on hypothesis
*)

(* shifting of hypothesises, all hypothesises which cannot be shifted (due to negative shifting) *)
let shift_hypothesises (hyps: hypothesises) (level: int) =
  NameMap.fold (fun name (prf, lemma) acc ->
    try 
      NameMap.add name (shift_term prf level, shift_term lemma level) acc
    with
      | DoudouException (Unshiftable_term _) -> acc
  ) hyps NameMap.empty

(* a function that check that all hypothesis are well typed *)
let check_hypothesis (defs: defs) (ctxt: context) (hyps: hypothesises) : unit =
  NameMap.iter (fun name (prf, lemma) -> 
    ignore(typecheck defs (ref ctxt) lemma (Type nopos));
    ignore(typecheck defs (ref ctxt) prf lemma)
  ) hyps

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
  a flag that check whenever needed that a proof_context and the goals are valid
*)

let force_check = ref true

(*
  checking a proof context and goals
*)
let check_proof_context (ctxt: proof_context) (goals: term list) : unit =
  ignore(check_hypothesis ctxt.defs ctxt.ctxt ctxt.hyps);
  ignore(List.iter (fun goal -> ignore(typecheck ctxt.defs (ref ctxt.ctxt) goal (Type nopos))) goals)

(*
  a proof_solver: a function that takes a proof_context and a goal and returns a proof_context together with a proof of the goal
*)
type proof_solver = proof_context -> term -> proof_context * term

(*
  a proof_context_transformer: a function that modifies the proof_context (such that it stay valid)
*)

(*
  for proving a term we might split a goal sequentially
  prfctxt: the original proof_context
  goals: a list of sub-goals together with thir solver function
  merge: a function that merges goals together

  here the proof_context can be extends all along the pass of solver, such that we get the proof_context of the last solver

*)
let split_goal_sequentially (ctxt: proof_context) (goals: (term * proof_solver) list) (merge: term list -> term) : proof_context * term =
  let ctxt, rev_prfs = List.fold_left (fun (ctxt, prfs) (goal, solver) ->
    let ctxt, prf = solver ctxt goal in
    ctxt, prf::prfs 
  ) (ctxt, []) goals in
  let prf = merge (List.rev rev_prfs) in
  if !force_check then check_proof_context ctxt (prf::rev_prfs);
  ctxt, prf
  
