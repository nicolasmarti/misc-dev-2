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
open Fol
open Proof

let proof_ctxt = empty_proof_context !fol_defs

(* test the initial proof_context *)
let _ = ignore(check_proof_context proof_ctxt [])

(* test the Show tactic *)
let _ = tactic_semantics (ShowGoal (Exact (Type nopos))) proof_ctxt (Type nopos)

(* test the Apply tactic *)
let _ = 
  try 
    let absurd = constante_symbol proof_ctxt.defs (Name "absurd") in
    ignore(tactic_semantics (ShowGoal (Apply (Cste (absurd, nopos)))) proof_ctxt (Type nopos))
  with
    | _ -> ()

let _ = 
  try 
    let disj = constante_symbol proof_ctxt.defs (Name "disj") in
    ignore(tactic_semantics (ShowGoal (Apply (Cste (disj, nopos)))) proof_ctxt (Type nopos))
  with
    | _ -> ()
      
(**********************************)
(* example of first order solving *)
(**********************************)

let _ = printf "\n\n------------------------------------------- First Order Solver Tests -------------------------------------------------\n\n"

open Fol_solver

let _ = fol_solver "{A B :: Type} -> A -> A"
let _ = fol_solver "{A B :: Type} -> (A /\\ B) -> (B /\\ A)"
let _ = fol_solver "{A B :: Type} -> (A \\/ B) -> (B \\/ A)"

