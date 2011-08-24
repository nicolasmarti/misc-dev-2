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

 
  here is an informal algorithm
  (* which actually is the opportunity to informally write the kind of tactics we want *)

  1) build an initially empty hypothesis

  2) sature the hypothesis (using the axiom of FOL + modus ponens, c.f. details bellow)
     
  3) try 
        solving the goal by tautology (using both hypothesis and the axiom of FOL, c.f. details bellow)
     if there is such a tautology returns its proof else continue to 4)

  4) here we present an informal pattern matching on the hypothesis and goal of the form:
     {H} |- G => action
     (* intuitively, {H} matches a subset of hypothesis, and G matches the goal 
        a pattern variable might appear more than once (and all its occurence should have the same unification)
     *)
     we trigger the action for the first pattern hyp that match the proof_context, if the resulting action fails then we rollback
     to the next choice
     
     _ |- A -> B => intro; 4)
     _ |- A /\\ B => apply (conj {A} {B}); 4)
     H :: A \\/ B |- _ => apply (disj {A} {B} H); 4)
     _ |- A \\/ B => (apply (left {A} {B}); 4)) || (apply (right {A} {B}); 4))

  * saturation (presented in the same pattern format as 4) above)
  here prf(H) means the proof term of H, and 

  H :: A /\\ B |- _ => add H1 := proj1 {A} {B} prf(H) :: A and H2 := proj2 {A} {B} prf(H) :: B in the hypothesis; remove H
  H1 :: A -> B, H2 :: A |- _ => add H1' := prf(H1) prf(H2) :: B; remove H1 
  H1 :: P, H2 :: ~ P |- _ => add H := contradiction {P} H1 H2 :: false
  H1 :: x = y, H2 :: P x |- _ => add H := congr {A} P x y H1 :: P y
  _ |- _ => done (* stop the saturation *)
  
  * tautology
  
  _ |- true => exact I
  _ |- (x :: A) = x => refl {A} x
  H :: A |- A => exact H
  H :: false |- G => exact (absurd {G} H)
 

  here is an attempt at writing the tactic in a string format:

  Tactic sature(cont) :=
    | H :: ?A /\\ ?B |- _ => add H1 := proj1 {?A} {?B} prf(H) :: ?A and H2 := proj2 {?A} {?B} prf(H) :: ?B in the hypothesis; remove H; sature(cont)
    | H1 :: ?A -> ?B, H2 :: ?A |- _ => add H1' := prf(H1) prf(H2) :: ?B; remove H1; sature(cont)
    | H1 :: ?P, H2 :: ~ ?P |- _ => add H := contradiction {?P} prf(H1) prf(H2) :: false; sature(cont)
    | H1 :: ?x = ?y, H2 :: ?P ?x |- _ => add H := congr {A} ?P ?x ?y prf(H1) :: ?P ?y; remove H2; sature(cont)
    | cont

  Tactic tauto :=
   | _ |- true => exact I
   | _ |- (?x :: ?A) = ?x => refl {?A} ?x
   | H :: ?A |- ?A => exact prf(H)
   | H :: false |- ?G => exact (absurd {?G} prf(H))

  Tactic FOL :=
    sature (
      | _ |- _ => tauto 
      | _ |- ?A -> ?B => intro; FOL
      | _ |- ?A /\\ ?B => apply (conj {?A} {?B}); FOL
      | H :: ?A \\/ ?B |- _ => apply (disj {?A} {?B} prf(H)); FOL
      | _ |- ?A \\/ ?B => (apply (left {?A} {?B}); FOL) || (apply (right {?A} {?B}); FOL)      
    )
  
*)

(*
  examples of formula:
  -------------------
*)

(* lemma: {A B :: Type} -> (A /\\ B) -> (B /\\ A) 
       
   proof: \\ {A B :: Type} (H :: A /\\ B) -> conj (proj2 H) (proj1 H)
*)


(* 
   lemma {A B :: Type} -> (A \\/ B) -> (B \\/ A) 

   proof: \\ {A B :: Type} (H :: A \\/ B) ->  disj H (\\ a -> right a) (\\ b -> left b)
*)


(*
  we are going to implement the solver as a tactic
*)


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
    (* we assure that the term is a valid formula *)
    if not (is_formula !fol_defs te) then raise (DoudouException (FreeError "The lemma is not a valid first order formula"));
    (* and we use the tactics *)
    raise (Failure "Not Yet Implemented")
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
