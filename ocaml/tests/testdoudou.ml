open Parser
open Printf
open Pprinter

open Doudou


(**************************)
(* example of definitions *)
(**************************)

let definition_ctxt = ref empty_context

let definition_defs = ref (empty_defs ())

let _ = printf "------------------------------------------- Definitions Tests -------------------------------------------------\n\n"

(* Logic *)

let _ = process_definition definition_defs definition_ctxt ~verbose:true "false :: Type"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "true :: Type"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "I :: true"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "[~) :  50 :: Type -> Type"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "contradiction :: {P :: Type} -> P -> ~ P -> false"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "absurd :: {P :: Type} -> false -> P"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "(/\\) : left, 40 :: Type -> Type -> Type"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "conj :: {A B :: Type} -> A -> B -> A /\\ B"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "proj1 :: {A B :: Type} -> A /\\ B -> A"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "proj2 :: {A B :: Type} -> A /\\ B -> B"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "(\\/) : left, 30 :: Type -> Type -> Type"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "left :: {A B :: Type} -> A -> A \\/ B"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "right :: {A B :: Type} -> B -> A \\/ B"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "disj :: {A B C :: Type} -> A \\/ B -> (A -> C) -> (B -> C) -> C"

(* Boolean *)

let _ = process_definition definition_defs definition_ctxt ~verbose:true "Bool :: Type"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "True :: Bool"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "False :: Bool"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "(||) : left, 20 :: Bool -> Bool -> Bool"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "True || _ := True"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "_ || True := True"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "False || False := False"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "(&&) : left, 30 :: Bool -> Bool -> Bool"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "_ && False := False"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "False && _ := False"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "True && True := True"

(* operators *)

let _ = process_definition definition_defs definition_ctxt ~verbose:true "plusType :: Type -> Type -> Type"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "(+) : left, 20 :: {A B :: Type} -> A -> B -> plusType A B"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "multType :: Type -> Type -> Type"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "(*) : right, 30 :: {A B :: Type} -> A -> B -> multType A B"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "(=) : no, 5 :: {A :: Type} -> A -> A -> Bool"

(* List *)

let _ = process_definition definition_defs definition_ctxt ~verbose:true "List :: Type -> Type"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "[[]] :: {A :: Type} -> List A"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "(:) : right, 10 :: {A :: Type} -> A -> List A -> List A"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "map :: {A B:: Type} -> (f:: A -> B) -> List A -> List B"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "map f [] := []"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "map f (hd:tl) := f hd : map f tl"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "(@) : right, 5 :: {A :: Type} -> List A -> List A -> List A"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "[] @ l := l"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "l @ [] := l"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "(hd:tl) @ l := hd:(tl @ l)"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "reverse :: {A :: Type} -> List A -> List A"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "reverse [] := []"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "reverse (hd:tl) := reverse tl @ (hd:[])"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "foldl :: {A B :: Type} -> (B -> A -> B) -> B -> List A -> B"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "foldl f acc [] := acc"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "foldl f acc (hd:tl) := foldl f (f acc hd) tl"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "foldr :: {A B :: Type} -> (A -> B -> B) -> List A -> B -> B"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "foldr f [] acc := acc"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "foldr f (hd:tl) acc := f hd (foldr f tl acc)"

(* Nat *)

let _ = process_definition definition_defs definition_ctxt ~verbose:true "Nat :: Type"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "O :: Nat"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "S :: Nat -> Nat"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "plusType Nat Nat := Nat"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "(+) {Nat} {Nat} O x := x"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "(+) {Nat} {Nat} x O := x"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "(+) {Nat} {Nat} (S x) y := S (x + y)"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "multType Nat Nat := Nat"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "(*) {Nat} {Nat} O x := O"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "(*) {Nat} {Nat} x O := O"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "(*) {Nat} {Nat} (S x) y := y + (x * y)"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "(=) {Nat} O O := True"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "(=) {Nat} (S _) O := False"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "(=) {Nat} O (S _) := False"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "(=) {Nat} (S x) (S y) := x = y"

(* Vector *)

let _ = process_definition definition_defs definition_ctxt ~verbose:true "Vec :: Type -> Nat -> Type"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "Empty :: {A :: Type} -> Vec A O"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "Next :: {A :: Type} -> {n:: Nat} -> A -> Vec A n -> Vec A (S n)"

(* pair *)

let _ = process_definition definition_defs definition_ctxt ~verbose:true "prod :: Type -> Type -> Type"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "pair :: {A B :: Type} -> A -> B -> prod A B"

(* dependant type fold *)

let _ = process_definition definition_defs definition_ctxt ~verbose:true "T :: Type -> Type -> Nat -> Type"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "T A B O := B"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "T A B (S n) := A -> T A B n"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "depfold :: {A B :: Type} -> (f:: B -> A -> B) -> B -> (n :: Nat) -> T A B n"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "depfold f acc O := acc"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "depfold {A} {B} f acc (S n) := \\ (x :: A) -> depfold f (f acc x) n)"

(* term examples *)

let _ = process_definition definition_defs definition_ctxt ~verbose:true "Type : ([] {Type})"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "Type : []"
let _ = process_definition definition_defs definition_ctxt ~verbose:true "Type:Type:[]"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "\\ {A::Type} (a::A) -> a"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "map"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "\\ (b :: Bool) -> b || False"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "map (\\ (b :: Bool) -> b || False) (True:False:[])"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "id :: {A :: Type} -> A -> A ~verbose:true "
let _ = process_definition definition_defs definition_ctxt ~verbose:true "id a := a ~verbose:true "

let _ = process_definition definition_defs definition_ctxt ~verbose:true "map id (Type : List Type : [])"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "map (\\ {A :: Type} (a :: A) -> a) (Type : List Type : [])"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "(Type : List Type : []) @ (Type : List Type : [])"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "reverse (Type : List Type : [])"


let _ = process_definition definition_defs definition_ctxt ~verbose:true "S O + S O"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "S O * S O"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "\\ {A :: Type} (a :: A) -> A"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "foldl ((+) {Nat} {Nat}) O (O : S O : [])"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "depfold ((+) {Nat} {Nat}) O (S (S O)) (S O) (S (S O))"

let _ = process_definition definition_defs definition_ctxt ~verbose:true "(~true \\/ false /\\ true) -> false"


(**********************)
(* example of tactics *)
(**********************)

let _ = printf "\n\n------------------------------------------- Tactics Tests -------------------------------------------------\n\n"

(* some test *)
open Proof

(*****************************************************************)
(*                one solver entry: a string                     *)
(*****************************************************************)

let tactic_solver (defs: defs) (ctxt: context ref) (t: tactic) (s: string) : unit = begin
  (* we set the parser *)
  let lines = stream_of_string s in
  let pb = build_parserbuffer lines in
  let pos = cur_pos pb in
  try 
    let te = parse_term defs pos pb in
    (* we typecheck the terms again Type *)
    let te, _ = typecheck defs ctxt te (Type nopos) in
    (* we ensure there is not free variable *)
    let [te] = flush_fvars ctxt [te] in
    if not (IndexSet.is_empty (fv_term te)) then raise (DoudouException (FreeError "There is still free variable in the term after typechecking!"));
    (* and create a proof context *)
    let proof_ctxt = { defs = defs; ctxt = !ctxt; hyps = NameMap.empty } in
    (* run the tactics *)
    let prf = tactic_semantics t proof_ctxt te in
    (* typecheck the result *)
    let prf, te = typecheck defs ctxt prf te in
    printf "%s\n\t::\n%s\n\n" (term2string !ctxt prf) (term2string !ctxt te)
  with
    | NoMatch -> 
      printf "parsing error: '%s'\n%s\n" (Buffer.contents pb.bufferstr) (errors2string pb);
      raise Pervasives.Exit
    | DoudouException err -> 
      (* we restore the context and defs *)
      printf "error:\n%s\n" (error2string err);
      raise Pervasives.Exit
    | CannotSolveGoal ->
      printf "cannot find a proof\n";
end

let goal1 = "{A :: Type} -> A -> A"

let tactic1 = Intro (["A"; "H"],
		     Cases [
		      PPVar "A", ["H", PPVar "A"], Exact (PPProof "H")
		     ]
)

let _ = tactic_solver (empty_defs ()) (ref empty_context) tactic1 goal1

let goal2 = "{A B :: Type} -> (A -> B) -> A -> B"

let tactic2 = Intro (["A"; "B"; "H"; "H1"],
		     Cases [
		      PPAVar, ["H1", PPImpl (PPVar "A", PPVar "B"); "H2", PPVar "A"],
		      AddHyp ("H", PPApp (PPProof "H1", [PPProof "H2", Explicit]), PPVar "B",
			      Cases [
				PPVar "A", ["H", PPVar "A"], Exact (PPProof "H")
			      ]				
		      )		      
		     ]
)

let _ = tactic_solver (empty_defs ()) (ref empty_context) tactic2 goal2


      
(**********************************)
(* example of first order solving *)
(**********************************)

let _ = printf "\n\n------------------------------------------- First Order Solver Tests -------------------------------------------------\n\n"

open Fol

open Fol_solver

let fol_tests_def = ref (!fol_defs)
let fol_tests_ctxt = ref (!fol_ctxt)

let _ = fol_solver fol_tests_def "true"

(* we enter constant symbols *)
let _ = process_definition fol_tests_def fol_tests_ctxt "A :: Type"
let _ = process_definition fol_tests_def fol_tests_ctxt "B :: Type"
let _ = fol_solver fol_tests_def "false -> A"
let _ = fol_solver fol_tests_def "(A /\\ B) -> (B /\\ A)"
let _ = fol_solver fol_tests_def "(A \\/ B) -> (B \\/ A)"


let _ = process_definition fol_tests_def fol_tests_ctxt "C :: Type"
let _ = fol_solver fol_tests_def "(A /\\ B /\\ C) -> (C /\\ B /\\ A)"
let _ = fol_solver fol_tests_def "(A \\/ B \\/ C) -> (C \\/ B \\/ A)"
let _ = fol_solver fol_tests_def "(A \\/ (B /\\ C)) -> (C \\/ A) /\\ (A \\/ B))"

let _ = process_definition fol_tests_def fol_tests_ctxt "ty :: Type"
let _ = process_definition fol_tests_def fol_tests_ctxt "P :: ty -> Type"
let _ = process_definition fol_tests_def fol_tests_ctxt "x :: ty"
let _ = process_definition fol_tests_def fol_tests_ctxt "y :: ty"
let _ = process_definition fol_tests_def fol_tests_ctxt "z :: ty"

let _ = fol_solver fol_tests_def "P x -> x = y -> y = z -> P z"

(***********************************)
(* example of interactive tactics  *)
(***********************************)

let _ = printf "\n\n------------------------------------------- Interactive Proof Mode tests  -------------------------------------------------\n\n"

let _ = printf "try: Intro H1 H2 H3 H4; Exact proof(H3) proof(H4)\n(then Enter and then CTRL-D\n"

let _ = tactic_solver (empty_defs ()) (ref empty_context) Interactive goal2
