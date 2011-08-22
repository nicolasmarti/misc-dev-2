open Doudou

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

  Here follow we describe more formally the set of types that we accept as formulae:

  formula := (name :: fo-formula) -> formula (* please note that the quantification can be Implicit, this is the forall *)
             | fo-formula
  fo-formula := atom | fo-formula opbin fo-formula | oppre fo-formula
  opbin := (/\\) | (\//) | (->)  
  oppre := [~)
  atom := predicate (term list) | term = term | name
  term := name | function (term list)

  as we are dealing with FOL, function and predicat are bounded var at the formula level (== constant names)
  
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
    

Rmq: we here keep all hypothesis in the same data structure, because we are working without theories (other than equality). In the case where we deal with theories, we would need to keep subset of H' (sorted by there predicate, and functions (in case of equality on there terms)), in order to call for decision procedure (which basically takes their own Hypothesis + a goal on their predicate)

  for the rest of the comments, we will use the following notation:

  H |- H' |- Prf :: G

  where H are the hypothesis corresponding to bound variables,
        H' are the derived hypothesis (ground terms under H |-)
        Prf is a proof of the goal G (?? noting the Prf that we are currently looking for)

*)

(* a working context *)
let fol_ctxt = ref empty_context

(* the definitions of the base logic *)
let fol_defs = ref empty_defs

(* this is the theorie for FOL in our LF (we take the (->) of our LF for implication) *)

let _ = process_definition defs ctxt "false :: Type"
let _ = process_definition defs ctxt "true :: Type"
let _ = process_definition defs ctxt "I :: true"

let _ = process_definition defs ctxt "[~) : 50 :: Type -> Type"
let _ = process_definition defs ctxt "contradiction :: {P :: Type} -> P -> ~ P -> false"
let _ = process_definition defs ctxt "absurd :: {P :: Type} -> false -> P"

let _ = process_definition defs ctxt "(/\\) : left, 40 :: Type -> Type -> Type"
let _ = process_definition defs ctxt "conj :: {A B :: Type} -> A -> B -> A /\\ B"
let _ = process_definition defs ctxt "proj1 :: {A B :: Type} -> A /\\ B -> A"
let _ = process_definition defs ctxt "proj2 :: {A B :: Type} -> A /\\ B -> B"

let _ = process_definition defs ctxt "(\\/) : left, 30 :: Type -> Type -> Type"
let _ = process_definition defs ctxt "left :: {A B :: Type} -> A -> A \\/ B"
let _ = process_definition defs ctxt "right :: {A B :: Type} -> B -> A \\/ B"
let _ = process_definition defs ctxt "disj :: {A B C :: Type} -> A \\/ B -> (A -> C) -> (B -> C) -> C"

(* this is the theorie of equality in of LF *)

let _ = process_definition defs ctxt "(=) : no, 20 :: {A :: Type} -> A -> A -> Type"
let _ = process_definition defs ctxt "refl :: {A :: Type} -> (a :: A) -> a = a"
let _ = process_definition defs ctxt "congr :: {A :: Type} -> (P :: A -> Type) -> (a b :: A) -> a = b -> P a -> P b"

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

*)

let _ = process_definition defs ctxt "\\ {A B :: Type} (H :: A /\\ B) -> conj (proj2 H) (proj1 H)"

(* {A B :: Type} -> (A \\/ B) -> (B \\/ A) *)

let _ = process_definition defs ctxt "
\\ {A B :: Type} (H :: A \\/ B) -> 
disj H (\\ a -> right a) (\\ b -> left b)
"

(*
  this the entry function for our prover:
  
  1) it pushes in a context the hypothesis (verifying that there types is in fo-formula)
  2) it verifies that the final goal is also in fo-formula

  it then calls the prover loops with the context, and empty derived hypothesis set, and the goal

  finally it returns the resulting proof

  basically, if everything went right
  step1 defs lemma = proof <-> defs , {} |- proof :: lemma

*)
let rec ifol_solver_entry (defs: defs) (goal: term) : term =
  let ctxt, goal = input_hypothesis defs empty_context goal in
  (* here we use lists ... but it would be better to use some set data-structure 
     the issue is that the equality function (basically unification with for result IndexMap.empty)
     depends on the context in which we are, and that I am not sure what semantics should have < and > 
     (possibly needs to look at optimization of fol theorem prover)
     
     our initial set of derived hypothesis is the empty set extends with our formula hypothesis
  *)
  let formula_hypothesis = raise (Failure "???") in
  let derived = extends_derived_hyps defs ctxt [] formula_hypothesis in
  ifol_solver_loop defs ctxt derived goal
(*
  this function is responsible to recursively check the types of the hypothesis (\in fo-formula)
  and input them into the context, returning the final goal (and checking it is in fo-formula)
*)
and input_hypothesis (defs: defs) (ctxt: context) (goal: term) : context * term =
  match goal with
    | Impl ((s, ty, n, _), goal, _) when is_fo_formula defs ctxt ty ->
      (* here we are sure that the hypothesis is ok *)
      (* we build a new frame for it *)
      let frame = build_new_frame s (shift_term ty 1) in
      (* append it to the context *)
      let ctxt = frame::ctxt in
      (* and recursively call the function *)
      input_hypothesis defs ctxt goal
    (* we have a fo-formula conclusion *)
    | te when is_fo_formula defs ctxt te ->
      (ctxt, te)
    (* otherwise, the formula is not in the fragment the solver can handle *)
    | _ -> raise (DoudouException (
      FreeError (String.concat "\n" ["the formula:"; term2string ctxt goal; "is not in the grament supported by our prover"])
    )
    )

(* the function that verifies that a term is in fo-formula *)
and is_fo_formula (defs: defs) (ctxt: context) (te: term) : bool =
  raise (Failure "is_fo_formula: NYI")

(* this function is the loop of the solver
   the derived hypothesis are supposed to be satured
   any caller of the function is responsible for that
*)
and ifol_solver_loop (defs: defs) (ctxt: context) (derived: (term * term) list) (goal: term) : term =
  raise (Failure "ifol_solver_loop: NYI")

(*
  this function extends a initial set of derived hypothesis with
  a new set of derived hypothesis  
*)
and extends_derived_hyps (defs: defs) (ctxt: context) (derived: (term * term) list) (new_derived: (term * term) list) : (term * term) list =
  raise (Failure "extends_derived_hyps: NYI")


