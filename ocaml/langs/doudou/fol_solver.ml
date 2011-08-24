(* just for nopos *)
open Parser
open Pprinter
open Printf

open Doudou
open Fol
open Proof

(*

  this is an attempt to build a intuitionistic first order solver
  that generate a doudou term

  after implementation of destruction it should be simpler

  for now we need the constructors AND destructors 

  In the litterature there exists several way to do:
  restricting ourselves to a fragment of the type (named fol therefore)
  
  * we translate our goal and the hypothesis in fol, and translate it into the target source of 
  an external theorem prover. afterward several possibilities
  1) if the prover returns ok, just returns an axioms (no proof term)
  2) if the prover returns ok + a trace:
      i) rebuild a proof term, from the trace
      ii) embedded in the LF a deduction system proved sound, and translate the trace in
          the deduction system

  2.ii) is the solution that needs the most powerfull LF, but should be the most powerfull
        - the deduction tree is reduce to its semantics, through a boolean test in LF (reflexion), thus the proof term is minimal (to the cost of reduction of terms in LF)
        - as all other solutions, the search is outside of LF and thus faster
        - avoid a lots of "bureaucracy"

        putting it in terms of signature
  
        (* the inductive type, that represent the fragment *)
        FOL :: Type

        (* a partial transformation from the LF terms to FOL terms *)
        toFOL :: Type -> Option FOL

        (* the semantics and its specification *)
        fromFOL :: FOL -> Type
       
        (* here we consider only the implication way that will allow reflexive proof *)
        (* note that this lemma is not a real one, as we cannot build a function from Type *)
        Lemma fromtoFOLSpecif :: forall (f::Type) fol, toFOL f = fol -> fromFOL fol -> f

        (* we need a deduction system *)
        deducSystRules :: FOL -> Type

        (* and its semantics, (we keep an environment in here) *)
        forall (fol :: FOL) (proof :: deducSyst fol), fromFOL fol


  but as said before, it should require more works on doudou (proper inductive types, Type stratification, test for completeness of functions, and termination checker). Which we will definitively do!!

  For now we will try to do something else:
  - define a theory in doudou
  - take a goal in this theory
  - try to solve the goal, keeping track of the trace generating the proof
  - rebuild the proof term (possibly of minimum size)

  This approach is reminiscent of 2.i).
  However it subtly differs in the sense that it is not external, but rather dedicated to some theory axiomatized (which should allow to tweek search more closely to the deduction system implied by the set of rules), and tighly linked to the underlying LF library.

  The base theory here is FOL (for now intuitionistic, but it might be extends with the excluded middle axiom for the classical variant), which should allow to implement a decision procedure. We also consider the equality, allowing to link underlying theory (like integers, constructors, ...) for SMT in the future

  We will start our reflexion from the following resolution calculus (using sequent calculus notations) 
  [modulo structural rules, which are the bureaucracy we would like to reduce for proof constructions !! 
   and that can be all be resume in this rule:
   X' \in X    Y \in Y'    X' |- Y'
   --------------------------------  SUB
               X |- Y
  ]

  ------- Ax
  A  |- A 

  X1 |- Z1, Y1  X2, Z2 |- Y2
  ----------------------------- Res (where sig = MGU(Z1, Z2))
       (X1, X2 |- Y1, Y2).sig

  ------------ REFL
    |- a = a

   X1 |- t = u, Y1   X2[t'/u] |- Y2[t'/u]
  ----------------------------------------- PARA (where sig = MGU(t, t')
        (X1, X2 |- Y1, Y2).sig

  
  here is an informal algorithm
  1) introduce all the quantification of formula in the context such that we have bounded variables
     corresponding to the hypothesis H, and the goal G

     H_i |- G

     under this context, once we have the proof Prf of G, we just need to lambda quantifiy it with the H_i to have our final proof

  2) we create the (initially empty) set of derived hypothesis H'

  3) we extend H'
     (basically, we create aliases for computations, something reminiscent to let ..., but here we avoid to create bounded variables)
     through the following actions (obviously modulo if the hypothesis is already in (H U H') or if we can replace an hypothesis in H' by a similar one but using a smaller term):
     -) if we have A /\\ B in (H U H') we enter the the Hypothesis A and B through proj1 and proj2
     -) for all equality (a = b) we generate new hypothesis using congr
     -) if we have P and ~ P then we derive false
     -) if we have A -> B and A in (H U H') then we can replace the implication by its conclusion (modus ponens)

  4) we try to solve the goal by tautology
     -) using Ax := (\ {A :: Type} (a :: A) -> a)
     -) using absurd if we generated false in 2)
     -) using I for the true goal
     -) using refl in case with have a goal of the form |- x = x

  5) if there is a goal remaining we have options:
     -) working on the goal:
        i) splitting a goal of the form |- A /\\ B (trying to solve both) and merging both proof using conj
        ii) splitting a goal of the form |- A \\/ B (launching to parallel research, using the smallest proof, our the one that finishes)
        
     -) working further on the hypothesis:
        i) either by trying to instantiate a universally quantified hypothesis
           -) first try to see if the goal and the conclusion "unifies"
           -) try to solve the needed hypothesis using (H U H'), and making the unresolved ones as goals
        ii) by splitting the hypothesis of the form A \\/ B, having to prove the goal with
            a new hypothesis of either A or B (which is a free variables), and joining the proof using disj (warning: in this setup the hypothesis needs to be shift, in order to keep the terms consistent with the new context)
    
     -) if previous search failed, then we might need to look for a contradiction
        


Rmq: we here keep all hypothesis in the same data structure, because we are working without theories (other than equality). In the case where we deal with theories, we would need to keep subset of H' (sorted by there predicate, and functions (in case of equality on there terms)), in order to call for decision procedure (which basically takes their own Hypothesis + a goal on their predicate)

  for the rest of the comments, we will use the following notation:

  H |- H' |- Prf :: G

  where H are the hypothesis corresponding to bound variables,
        H' are the derived hypothesis (ground terms under H |-)
        Prf is a proof of the goal G (?? noting the Prf that we are currently looking for)

*)

(*
  examples of formula:
  -------------------
*)

(* {A B :: Type} -> (A /\\ B) -> (B /\\ A) 
   
   1), 2)
   {{A :: Type}; {B :: Type}; (H :: A /\\ B)} |- {} |- ?? :: B /\\ A

   3)
   {{A :: Type}; {B :: Type}; (H :: A /\\ B)} |- 
   {(proj1 H :: A); (proj2 H :: B)} |- ?? :: B /\\ A

   4) we cannot do anything

   5)
   we split and recursively try to solve
   
   {{A :: Type}; {B :: Type}; (H :: A /\\ B)} |- 
   {(proj1 H :: A); (proj2 H :: B)} |- ?? :: B 

   {{A :: Type}; {B :: Type}; (H :: A /\\ B)} |- 
   {(proj1 H :: A); (proj2 H :: B)} |- ?? :: A

   next steps 4) we solve both

   {{A :: Type}; {B :: Type}; (H :: A /\\ B)} |- 
   {(proj1 H :: A); (proj2 H :: B)} |- proj2 H :: B 
   
   {{A :: Type}; {B :: Type}; (H :: A /\\ B)} |- 
   {(proj1 H :: A); (proj2 H :: B)} |- proj1 H :: A

   returning in 5) we rebuild the proof

   {{A :: Type}; {B :: Type}; (H :: A /\\ B)} |- 
   {(proj1 H :: A); (proj2 H :: B)} |- conj (proj2 H) (proj1 H) :: B /\\ A
   
   the algorithm returns:
   
   \\ {A B :: Type} (H :: A /\\ B) -> conj (proj2 H) (proj1 H) ::
   {A B :: Type} -> (H :: A /\\ B) -> B /\\ A

   let _ = process_definition defs ctxt "\\ {A B :: Type} (H :: A /\\ B) -> conj (proj2 H) (proj1 H)"
*)


(* 
   {A B :: Type} -> (A \\/ B) -> (B \\/ A) 

   let _ = process_definition defs ctxt "
   \\ {A B :: Type} (H :: A \\/ B) -> 
   disj H (\\ a -> right a) (\\ b -> left b)
   "
*)


(*
  a flag that force type checking check all along the solver 
*)
let force_typecheck = ref true

let debug = ref false


(*
  this the entry function for our prover:
*)
let rec fol_solver_entry (goal: term) : term =

  (* we build our working context *)
  let ctxt = empty_proof_context !fol_defs in
  
  raise (Failure "Not yet implemented")


(*****************************************************************)
(*                one solver entry: a string                     *)
(*****************************************************************)

let fol_solver (s: string) : unit = 
  (* we set the parser *)
  let lines = stream_of_string s in
  let pb = build_parserbuffer lines in
  let pos = cur_pos pb in
  try 
    let te = parse_term !fol_defs pos pb in
    (* we typecheck the fol formula again Type *)
    let ctxt = ref empty_context in
    let te, _ = typecheck !fol_defs ctxt te (Type nopos) in
    (* we ensure there is not free variable *)
    let [te] = flush_fvars ctxt [te] in
    if not (IndexSet.is_empty (fv_term te)) then raise (DoudouException (FreeError "There is still free variable in the term after typechecking!"));
    (* we call the solver *)
    let proof = fol_solver_entry te in
    (* we show the result *)
    printf "Term |- %s :: %s \n" (term2string !ctxt proof) (term2string !ctxt te)
  with
    | NoMatch -> 
      printf "parsing error: '%s'\n%s\n" (Buffer.contents pb.bufferstr) (errors2string pb);
      raise Pervasives.Exit
    | DoudouException err -> 
      (* we restore the context and defs *)
      printf "error:\n%s\n" (error2string err);
      raise Pervasives.Exit

(*
  missing modus ponens
let _ = solve "{A B :: Type} -> (A -> B) -> A -> B"
*)
