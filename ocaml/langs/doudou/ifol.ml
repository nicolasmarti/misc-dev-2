open Doudou

(*

  this is an attempt to build a intuitionistic first order solver
  that generate a doudou term

  after implementation of destruction it should be simpler

  for now we need the constructors AND destructors 

*)

(* a working context *)
let fol_ctxt = ref empty_context

(* the definitions of the base logic *)
let fol_defs = ref empty_defs

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

(*
  examples of formula:
  -------------------
*)

(* {A B :: Type} -> (A /\\ B) -> (B /\\ A) *)

let _ = process_definition defs ctxt "\\ {A B :: Type} (H :: A /\\ B) -> conj (proj2 H) (proj1 H)"

(* {A B :: Type} -> (A \\/ B) -> (B \\/ A) *)

let _ = process_definition defs ctxt "
\\ {A B :: Type} (H :: A \\/ B) -> 
disj {A} {B} {A \\/ B} H (\\ a -> right a) (\\ b -> left b)
"
