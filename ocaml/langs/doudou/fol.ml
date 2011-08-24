open Doudou

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

let _ = process_definition fol_defs fol_ctxt "false :: Type"
let _ = process_definition fol_defs fol_ctxt "true :: Type"
let _ = process_definition fol_defs fol_ctxt "I :: true"

let _ = process_definition fol_defs fol_ctxt "[~) : 50 :: Type -> Type"
let _ = process_definition fol_defs fol_ctxt "contradiction :: {P :: Type} -> P -> ~ P -> false"
let _ = process_definition fol_defs fol_ctxt "absurd :: {P :: Type} -> false -> P"

let _ = process_definition fol_defs fol_ctxt "(/\\) : left, 40 :: Type -> Type -> Type"
let _ = process_definition fol_defs fol_ctxt "conj :: {A B :: Type} -> A -> B -> A /\\ B"
let _ = process_definition fol_defs fol_ctxt "proj1 :: {A B :: Type} -> A /\\ B -> A"
let _ = process_definition fol_defs fol_ctxt "proj2 :: {A B :: Type} -> A /\\ B -> B"

let _ = process_definition fol_defs fol_ctxt "(\\/) : left, 30 :: Type -> Type -> Type"
let _ = process_definition fol_defs fol_ctxt "left :: {A B :: Type} -> A -> A \\/ B"
let _ = process_definition fol_defs fol_ctxt "right :: {A B :: Type} -> B -> A \\/ B"
let _ = process_definition fol_defs fol_ctxt "disj :: {A B C :: Type} -> A \\/ B -> (A -> C) -> (B -> C) -> C"

(* this is the theorie of equality in of LF *)

let _ = process_definition fol_defs fol_ctxt "(=) : no, 20 :: {A :: Type} -> A -> A -> Type"
let _ = process_definition fol_defs fol_ctxt "refl :: {A :: Type} -> (a :: A) -> a = a"
let _ = process_definition fol_defs fol_ctxt "congr :: {A :: Type} -> (P :: A -> Type) -> (a b :: A) -> a = b -> P a -> P b"

(* functions that verifies that a term is in 
   - formula 
   - fo-formula
   - atom
   - term

   the level keep track of the frontier between free variable of the whole formula and quantified vars
   
*)
let rec is_formula (defs: defs) ?(level: int = 0) (te: term) : bool =
  match te with       
    | Impl ((_, ty, _, _), te, _) ->
      is_fo_formula defs ty level && is_formula defs ~level:(level + 1) te 
    | Type _ -> true
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

    | _ -> false

and is_term (defs: defs) (te: term) (level: int) : bool =
  match te with
    | TVar (i, _) -> true

    | App (TVar (i, _), args, _) when i >= level ->
      List.fold_left (fun acc hd -> acc && is_term defs hd level) true (filter_explicit args)

    | _ -> false

