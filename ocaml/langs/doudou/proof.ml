open Parser
open Pprinter
open Doudou

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
  a proof_solver: a function that takes a proof_context and a goal and returns a proof_context together with a proof of the goal
*)
type proof_solver = proof_context -> term -> proof_context * term

(*
  a proof_context_transformer: a function that modifies the proof_context (such that it stay valid)
*)

type proof_context_transformer = proof_context -> proof_context

(*
  a goal_transformer: a function that modifies the goal (such that it stay valid under the proof_context)
*)

type goal_transformer = proof_context -> term -> term

(*
  for witenessing a term we might split a goal in different subgoals which need all to be proved

  prfctxt: the original proof_context
  goals: a list of sub-goals together with thir solver function
  merge: a function that merges goals together

  the proof is sequential, in order, the context is shared/extends

*)
let split_goal_allneeded (ctxt: proof_context) (goals: (term * proof_solver) list) (merge: term list -> term) : proof_context * term =
  (* we traverse the goals and their provers *)
  let ctxt, rev_prfs = List.fold_left (fun (ctxt, prfs) (goal, solver) ->
    let ctxt, prf = solver ctxt goal in
    if !force_check then check_proof_context ctxt [prf, goal];
    ctxt, prf::prfs 
  ) (ctxt, []) goals in
  (* we merge the proofs in the right order *)
  let prf = merge (List.rev rev_prfs) in
  (* checking if we wish to *)
  if !force_check then check_proof_context ctxt [];
  (* returning the result*)
  ctxt, prf

(*
  for witenessing a term we might split a goal in different possible subgoals of which only one need to be solved

  prfctxt: the original proof_context
  goals: a list of sub-goals together with their solver function and the function to rebuild the proof

  the contexts are not shared

*)
let split_goal_oneneeded (ctxt: proof_context) (goals: (term * proof_solver * (term -> term)) list) : proof_context * term =
  (* we try all the goals *)
  let res = fold_stop (fun () (goal, solver, prf_builder) ->
    try
      let ctxt, prf = solver ctxt goal in
      if !force_check then check_proof_context ctxt [prf, goal];
      let prf = prf_builder prf in
      Right (ctxt, prf)
    with
      | CannotSolveGoal -> Left ()
  ) () goals in
  match res with
    (* we cannot find any proof for the goals *)
    | Left () ->
      raise CannotSolveGoal
    | Right res -> res

(*
  when the goal is an Impl, we might want to introduce the quantification, 
  prove the goal and quantify it by a Lambda
*)
let introduce_impl (ctxt: proof_context) (goal: term) (solver: proof_solver) : proof_context * term =
  match goal with
    (* an implication, we can do a introduction *)
    | Impl (q, body, pos) ->
      (* quantifying the Impl *)
      let ctxt = push_quantification ctxt q in
      (* try to solve the goal *)
      let ctxt, prf = solver ctxt body in
      (* do a check *)
      if !force_check then check_proof_context ctxt [prf, body];
      (* pop the quantification *)
      let ctxt, q, prf = pop_quantification ctxt prf in
      (* rebuilt the proof *)
      let prf = Lambda (q, prf, nopos) in
      (* do a check *)
      if !force_check then check_proof_context ctxt [prf, goal];
      (* return the result *)
      ctxt, prf
    (* not an implication, cannot introduce  *)
    | _ -> raise CannotSolveGoal

(*
  
*)
