open Doudou
open Printf
(*
  this is an axiomatization for (intuitionistic) first order logic (without existential) with equality in doudou LF
 
  we also provide a function which verifies that a LF terms is a valid formula of the folowing form:

  formula := (name :: fo-formula) -> formula (* please note that the quantification can be Implicit, this is the forall *) | fo-formula
  fo-formula := atom | fo-formula opbin fo-formula | oppre fo-formula
  opbin := (/\\) | (\//) | (->)  
  oppre := [~)
  atom := predicate (term list) | term = term | name
  term := name | function (term list)

*)

(* a working context *)
let fol_ctxt = ref empty_context

(* the definitions of the base logic *)
let fol_defs = ref (empty_defs ())

(* this is the theorie for FOL in our LF (we take the (->) of our LF for implication) *)

let fol_definitions = "
false :: Type :=

true :: Type := | I :: true

[~) : 50 :: Type -> Type
contradiction :: {P :: Type} -> P -> ~ P -> false
absurd :: {P :: Type} -> false -> P

(/\\) : left, 40 (A B :: Type) :: Type := 
| conj :: A -> B -> A /\\ B

proj1 :: {A B :: Type} -> A /\\ B -> A
proj2 :: {A B :: Type} -> A /\\ B -> B

(\\/) : left, 30 (A B :: Type) :: Type :=
| left :: A -> A \\/ B
| right :: B -> A \\/ B

disj :: {A B C :: Type} -> A \\/ B -> (A -> C) -> (B -> C) -> C

(=) : no, 20 {A:: Type} (a :: A) :: A -> Type := 
| refl :: a = a

congr :: {A :: Type} -> (P :: A -> Type) -> (a b :: A) -> a = b -> P a -> P b
"

let _ = parse_process_definitions fol_defs fol_ctxt ~verbose:false fol_definitions

(* functions that verifies that a term is in 
   - formula 
   - fo-formula
   - atom
   - term

   the level keep track of the frontier between free variable of the whole formula and quantified vars
   
*)
let rec is_formula (defs: defs) ?(level: int = 0) (te: term) : bool =
  match te with       
    | Impl ((_, Type _, Implicit, _), te, _) ->
      is_formula defs ~level:(level + 1) te 

    | Impl ((_, ty, Explicit, _), te, _) ->
      is_formula defs ~level:level ty && is_formula defs ~level:(level + 1) te 

    | _ -> is_fo_formula defs te level
    
and is_fo_formula (defs: defs) (te: term) (level: int) : bool =
  match te with
    | App (Cste (s, _), args, _) when List.mem (symbol2string s) ["(/\\)"; "(\\/)"] && List.length args = 2 ->
      List.fold_left (fun acc (hd, _) -> acc && is_fo_formula defs hd level) true args

    | App (Cste (s, _), args, _) when List.mem (symbol2string s) ["[~)"] && List.length args = 1 ->
      List.fold_left (fun acc (hd, _) -> acc && is_fo_formula defs hd level) true args

    | _ -> is_atom defs te level

and is_atom (defs: defs) (te: term) (level: int) : bool =
  match te with
    | App (Cste (s, _), args, _) when symbol2string s = "(=)" && List.length (filter_explicit args) = 2 ->
      List.fold_left (fun acc hd -> acc && is_term defs hd level) true (filter_explicit args)

    | App (Cste (s, _), args, _) ->
      List.fold_left (fun acc hd -> acc && is_term defs hd level) true (filter_explicit args)

    | App (TVar (i, _), args, _) when i >= level ->
      List.fold_left (fun acc hd -> acc && is_term defs hd level) true (filter_explicit args)

    | TVar (i, _) -> true

    | Cste (s, _) -> true

    | _ -> false

and is_term (defs: defs) (te: term) (level: int) : bool =
  match te with
    | TVar (i, _) -> true

    | Cste _ -> true

    | App (TVar (i, _), args, _) when i >= level ->
      List.fold_left (fun acc hd -> acc && is_term defs hd level) true (filter_explicit args)

    | _ -> false

