(*
  This file is part of Mymms.

  Mymms is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  Mymms is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with Mymms.  If not, see <http://www.gnu.org/licenses/>.

  Copyright (C) Nicolas Marti
*)

open Definition;;
open Ast;;
open Universe;;
open Listext;;
open Pprinter;;
open Printf;;

type defnature =
  | DataDef
  | FunctionDef
  | TypeDef
  | UnknownDef
;;

class virtual ['a] pObj =
object 
  method virtual get_name: string
  method virtual get_type: 'a
  method virtual equal: 'a pObj -> bool
  method virtual pprint: 'a list -> token list
  method virtual exec: 'a list -> ('a * 'a * defnature) objdef -> 'a
  method virtual show: string
  method virtual uuid: (float * float * float)
end;;

type name = string;;

(* there is no terminaison here ... *)
(* var with negative value are free *)
type term =
    | Type of univ_level
    | Cste of name
    | Obj of term pObj
    | Var of int
    | Let of (name * term * term)
    | Lambda of (name * term * nature) * term
    | Forall of (name * term * nature) * term
    | Phi of name * (name * term * nature) list * term * terminaison_pattern * term
    | Ind of name * (name * term * nature) list * term * term list

    (* bool is the true if the application is implicit *)
    | App of (term * bool) list
	
    (* term to destruct, list of destructors, returned type, destruct inductive type *)	
    | Match of term * ((term * term) list) * term
	(*
    | Match2 of term * term list * term
	*)
    | Constr of int * term
	
;;

(* *)
let rec containsqv (t:term) (v: int) : bool =
  match t with
    | Type n -> false
    | Cste n -> false
    | Obj o -> false
    | Var x -> (x = v)
    | Let (n, t1, t2) -> (
	if (containsqv t1 v) then true
	else containsqv t2 (v+1)
      )	
    | Lambda ((x, t1, n), t2) -> (
	if (containsqv t1 v) then true
	else containsqv t2 (v+1)
      )
    | Forall ((x, t1, n), t2) -> (
	if (containsqv t1 v) then true
	else containsqv t2 (v+1)
      )
    | App l -> List.fold_left (fun acc hd -> if acc then acc else (containsqv (fst hd) v)) false l
    | Phi (x, l, ty, terminaison, te) -> (
	false
      )
    | Ind (x, l, ty, lcons) -> (
	false
      )
    | Constr (n, te) -> (
	false
      )
    | Match (te, ldes, ret) -> (
	false
      )
    | Match (te, ldes, ret) -> (
	false
      )
    | _ -> raise (Failure "containsqv: case not supported")

;;

let rec term2token (t: term) (show_univ: bool) (lv: string list): token list =
  match t with
    | Type ul -> (Verbatim "Type") :: if show_univ then (Verbatim "(") :: (univ_level2token ul) @ (Verbatim ")") :: [] else []
    | Cste n -> (*(Verbatim "[[") ::*) (Verbatim n) ::(* (Verbatim "]]") :: *)[]
    | Obj o -> 	o#pprint []
    | Var i -> (
	if (i >= 0) then (
	  try 
	    (Verbatim (List.nth lv i)) :: []
	  with
	    | _ -> (Verbatim "<") :: (Verbatim (string_of_int i)) :: (Verbatim ">") :: []
	)
	else
	  (Verbatim "[") :: (Verbatim (string_of_int i)) :: (Verbatim "]") :: []
	)
    | Let (n, te1, te2) ->
	let t1 = Box (term2token te1 show_univ lv) in
	let t2 = Box (term2token te2 show_univ (n::lv)) in
	  ((Verbatim "let") :: (Space 1) :: (Verbatim n) :: (Space 1) :: (Verbatim ":=") :: (Space 1) :: t1 :: (Space 1) :: (Verbatim "in") :: (Space 1) :: t2 :: [])
    | App l -> (concatenate (Space 1) (List.map (fun hd -> 
						   let b = 
						     match fst hd with
						       | App l2 ->
							   if List.length l2 > 1 then
							     (Verbatim "(") :: (Box (term2token (fst hd) show_univ lv)) :: (Verbatim ")") :: []
							   else
							     (Box (term2token (fst hd) show_univ lv)) :: []
						       | _ -> (Box (term2token (fst hd) show_univ lv)) :: []
						   in 
						     if (snd hd) then
						       (Verbatim "[") :: b @ (Verbatim "]") :: []
						     else
						       b						       
						)				    
					 l
				      )
	       )
    | Lambda ((v, t1, n), t2) -> (
	
	let t1 = Box (term2token t1 show_univ lv) in
	let t2 = Box (term2token t2 show_univ (v::lv)) in
	let (a, b) = 
	  match n with
	    | Implicite -> (Verbatim "[", (Verbatim "] ->"))
	    | Explicite -> (Verbatim "(", (Verbatim ") ->"))
	    | Hidden -> (Verbatim "{", (Verbatim "} ->"))
	in
	  ((Verbatim "\\") :: (Space 1) :: a :: (Verbatim v) :: (Verbatim ":") :: (Space 1) :: t1 :: b :: (Space 1) :: t2 :: [])

      )
    | Forall ((v, t1, n), t2) -> (
	let t1' = Box (term2token t1 show_univ lv) in
	let t2' = Box (term2token t2 show_univ (v::lv)) in
	let (a, b) = 
	  match n with
	    | Implicite -> (Verbatim "[", (Verbatim "]"))
	    | Explicite -> (Verbatim "(", (Verbatim ")"))
	    | Hidden -> (Verbatim "{", (Verbatim "}"))
	in
	  if (not (containsqv t2 0)) then
	    (a :: t1' :: b :: (Space 1) :: (Verbatim "->") :: (Space 1) :: t2' :: [])
	  else
	    ((Verbatim "V") :: (Space 1) :: a :: (Verbatim v) :: (Verbatim ":") :: (Space 1) :: t1' :: b :: (Verbatim ".") :: (Space 1) :: t2' :: [])
      )

    | Ind(x, largs, ty, lcons) -> 
	(Verbatim "Inductive") :: 
	  (Space 1) ::
	  (Verbatim x) :: 
	  (Space 1) ::
	  (List.map (fun (x, ty, n) ->
		       Box (
			 let (a, b) = 
			   match n with
			     | Implicite -> (Verbatim "[", (Verbatim "]"))
			     | Explicite -> (Verbatim "(", (Verbatim ")"))
			     | Hidden -> (Verbatim "{", (Verbatim "}"))
			 in
			   a :: (Verbatim x) :: (Verbatim ":") :: (Space 1) :: 
			     (term2token ty show_univ lv)
			      @ b :: (Space 1) :: []
		       )
		    ) largs
	  ) @ (Verbatim ":") :: (Space 1) :: (term2token ty show_univ lv) @ (Verbatim ":=") ::
	  Newline ::
	  (List.fold_left (fun acc hd ->
			     acc @ Box (
			       (Verbatim "|") :: (Space 1) :: (term2token hd show_univ (x :: (List.rev (List.map (fun (x, ty, n) -> x) largs)) @ lv))
			     ) :: Newline :: []
			  ) [] lcons
	  )

    | Phi(x, largs, ty, _, body) -> 
	(Verbatim "Recursive") :: 
	  (Space 1) ::
	  (Verbatim x) :: 
	  (Space 1) ::
	  (snd (List.fold_left (	     
		  fun acc (x, ty, n) ->
		    ((x::(fst acc)),
		       (snd acc) @ Box (
			 let (a, b) = 
			   match n with
			     | Implicite -> (Verbatim "[", (Verbatim "]"))
			     | Explicite -> (Verbatim "(", (Verbatim ")"))
			     | Hidden -> (Verbatim "{", (Verbatim "}"))
			 in
			   a :: (Verbatim x) :: (Verbatim ":") :: (Space 1) :: 
			(term2token ty show_univ ((fst acc) @ lv))
			   @ b :: (Space 1) :: []
		       ) :: []
		    )
		) ([], []) largs
	       )
	  ) @ (Verbatim ":") :: (Space 1) :: (term2token ty show_univ ((List.rev (List.map (fun (x, ty, n) -> x) largs)) @ lv)) @ (Space 1) :: (Verbatim ":=") :: 
	  Newline ::
	  (term2token body show_univ (x :: (List.rev (List.map (fun (x, ty, n) -> x) largs)) @ lv))	  

    | Constr (n, te) -> (Verbatim "Constr") :: (Space 1) :: (Verbatim (string_of_int n)) :: (Space 1) :: (Verbatim "of") :: (Space 1) :: (term2token te show_univ lv)
	
    | Match (te, ldes, retty) ->
	(Verbatim "match") :: (Space 1) :: (term2token te show_univ lv) @ (Space 1) :: (Verbatim "returns") :: (Space 1) :: (term2token retty show_univ lv) @ (Space 1) :: (Verbatim "with") :: Newline ::
	  (List.fold_left (fun acc hd ->
			     acc @ Box (
			       (Verbatim "|") :: (Space 1) :: (term2token (fst hd) show_univ lv) @ (Space 1) :: (Verbatim "==>") :: (Space 1) :: (term2token (snd hd) show_univ lv)) :: Newline :: []
			  ) [] ldes
	  )
;;

let pprintterm t show_univ =
  let t = term2token t show_univ [] in
  let t = Box t in
  let b = token2box t 80 2 in
    printbox b
;;

(* set of free variable *)
module OrderedFreeVar = 
    struct
      type t = int
      let compare (x: int) (y: int) = (x - y)
    end;;

module FreeVarSet = Set.Make(OrderedFreeVar);; 
module FreeVarMap = Map.Make(OrderedFreeVar);; 

let fvsin e s = FreeVarSet.subset (FreeVarSet.singleton e) s;;

let rec fv (te: term) : FreeVarSet.t =
  match te with
    | Type n -> FreeVarSet.empty
    | Cste n -> FreeVarSet.empty
    | Var x -> if (x < 0) then FreeVarSet.singleton x else FreeVarSet.empty
    | Obj o -> FreeVarSet.empty
    | Let (n, t1, t2) -> FreeVarSet.union (fv t1) (fv t2)
    | Lambda ((x, t1, n), t2) -> FreeVarSet.union (fv t1) (fv t2)
    | Forall ((x, t1, n), t2) -> FreeVarSet.union (fv t1) (fv t2)
    | Phi (x, l, ty, terminaison, te) -> 
	FreeVarSet.union 
	  (List.fold_right (
	     fun (_, te, _) acc ->
	       FreeVarSet.union (fv te) acc
	   ) l FreeVarSet.empty 
	  )
	  (FreeVarSet.union (fv ty) (fv te))
    | Ind (x, l, ty, lcons) -> 
	FreeVarSet.union 
	  (List.fold_right (
	     fun (_, te, _) acc ->
	       FreeVarSet.union (fv te) acc
	   ) l FreeVarSet.empty 
	  )
	  (FreeVarSet.union (fv ty) (
	     (List.fold_right (
		fun hd acc ->
		  FreeVarSet.union (fv hd) acc
	      ) lcons FreeVarSet.empty 
	     )
	   )
	  )
    | Constr (n, te) -> fv te
    | Match (te, ldes, ret) -> 
	FreeVarSet.union
	  (fv te)
	  (FreeVarSet.union
	     (
	       (List.fold_right (
		  fun hd acc ->
		    FreeVarSet.union (FreeVarSet.diff (fv (snd hd)) (fv (fst hd))) acc
		) ldes FreeVarSet.empty 
	       )  
	     )
	     (fv ret)
	  )
    | App l -> (List.fold_right (
		  fun (hd, _) acc ->
		    FreeVarSet.union (fv hd) acc
		) l FreeVarSet.empty 
	       )  
;;

exception MshiftException;;

(* shift of quantified-free variables *)
let rec shift_var (te: term) (delta: int) : term =
  shift_var' te 0 delta
and shift_var' (te: term) (level: int) (delta: int) : term =
  match te with
    | Type n -> Type n
    | Cste n -> Cste n
    | Var x -> (
	if (x < 0) then Var x
	else 
	  if (x >= level) then (
	    if (x + delta < level) then
	      raise MshiftException
	    else
	      Var (x + delta)
	  ) else 
	    Var x     
      )
    | Obj o -> Obj o
    | Let (n, t1, t2) ->
	Let (n, shift_var' t1 level delta, shift_var' t2 (level + 1) delta)
    | Lambda ((x, t1, n), t2) ->
	Lambda ((x, shift_var' t1 level delta, n), shift_var' t2 (level + 1) delta)
    | Forall ((x, t1, n), t2) ->
	Forall ((x, shift_var' t1 level delta, n), shift_var' t2 (level + 1) delta)
    | Phi (x, l, ty, terminaison, te) ->
	Phi (x, 
	     List.map (
	       fun ((hd1, hd2, hd3), hd4) ->
		 (hd1, shift_var' hd2 hd4 delta, hd3)
	     ) (List.combine l (iota 0 (List.length l - 1))) , 
	     shift_var' ty (List.length l) delta, 
	     terminaison,
	     shift_var' te (List.length l + 1) delta
	    )
    | Ind (x, l, ty, lcons) ->
	Ind (x,
	     List.map (
	       fun ((hd1, hd2, hd3), hd4) ->
		 (hd1, shift_var' hd2 hd4 delta, hd3)
	     ) (List.combine l (iota 0 (List.length l - 1))) , 
	     shift_var' ty (List.length l) delta, 
	     List.map (fun hd -> shift_var' hd (List.length l + 1) delta) lcons
	    )
    | Constr (n, te) -> Constr (n, shift_var' te level delta)
    | Match (te, ldes, ret) ->
	Match (shift_var' te level delta,
	       List.map (fun hd -> (shift_var' (fst hd) level delta, shift_var' (snd hd) level delta)) ldes,
	       (shift_var' ret level delta)
	      )
    | App l -> App (List.map (fun (hd1, hd2) -> (shift_var' hd1 level delta, hd2)) l)
;;


(* change hidden in explicit *)
let rec hidden2explicite (te: term) =
  match te with
    | Forall ((x, ty, Hidden), te) ->
	Forall ((x, ty, Explicite), hidden2explicite te)
    | Forall ((x, ty, n), te) ->
	Forall ((x, ty, n), hidden2explicite te)
    | Lambda ((x, ty, Hidden), te) ->
	Lambda ((x, ty, Explicite), hidden2explicite te)
    | Lambda ((x, ty, n), te) ->
	Lambda ((x, ty, n), hidden2explicite te)
    | _ -> te
;;

(* extraction *)
let rec extract (te: term) : term =
  match te with
    | Type n -> Type n
    | Cste n -> Cste n
    | Var x -> Var x
    | Obj o -> Obj o
    | Let (n, t1, t2) ->
	Let (n, extract t1, extract t2)
    | Lambda ((x, t1, Implicite), t2) ->
	extract (shift_var t2 (-1))
    | Lambda ((x, t1, _), t2) ->
	Lambda ((x, Type Zero, Explicite), extract t2)
    | Forall ((x, t1, n), t2) ->
	Forall ((x, extract t1, n), extract t2)

    (* this is not tested ... *)
    | Phi (x, l, ty, terminaison, te) ->
	let (_, l', te) = fold_left2 (
	  fun (acc1, acc2, acc3) (hd1, hd2, hd3) tl ->
	    if (hd3 = Implicite) then (
	      
	      ((acc1 - 1, ((hd1, extract hd2, hd3)::acc2), shift_var' acc3 acc1 (-1)), 
	       List.map (
		 fun ((hd1, hd2, hd3), hd4) ->
		   (hd1, shift_var' hd2 hd4 (-1), hd3)
	       ) (List.combine tl (iota acc1 (acc1 + List.length tl - 1)))
	      )

	    ) else 
	      ((acc1 - 1, ((hd1, extract hd2, hd3)::acc2), acc3), tl)
	      
	) (List.length l + 1, [], te) l in
	  Phi (x, l', extract ty, terminaison, extract te)

    | Ind (x, l, ty, lcons) ->
	let l' = List.fold_right (
	  fun (hd1, hd2, hd3) acc ->
	    (hd1, extract hd2, hd3)::acc
	) l [] in
	let lcons' = List.map extract lcons in
	  Ind (x, l', extract ty, lcons')
    | Constr (n, te) -> Constr (n, extract te)
    | Match (te, ldes, ret) ->
	let ldes' = List.map (fun hd -> (extract (fst hd), extract (snd hd))) ldes in
	  Match (extract te, ldes', (extract ret))
    | App l ->
	App (List.fold_right (fun (hd1, hd2) acc -> 
				if hd2 then
				  acc
				else
				  (hd1, false)::acc
		       ) l []
	    )
;;
	  
(* substitution and unification *)
(* as it goes from free variable to terms, the int must be negative *)
type substitution = (int * term) list
;;

type unification =
  | Mgu of substitution * univ_level_constraint list
  | NoMgu of int list (* a list a problematic variable (for match termchecking rule) *)
  | DnkMgu
;;

let shift_var_substitution (s: substitution) (delta: int) : substitution =
  List.fold_right (
    fun (hd1, hd2) acc ->
      (
	(if (hd1 < 0) then hd1
	 else 
	   if (hd1 + delta < 0) then
	     raise MshiftException
	   else
	     (hd1 + delta)	     
	)
	  , shift_var hd2 delta)::acc
  ) s []
;;

let shift_var_substitution_err (s: substitution) (delta: int) : substitution =
  List.fold_right (
    fun (hd1, hd2) acc ->
      try 
	((if (hd1 < 0) then hd1
	  else 
	    if (hd1 + delta < 0) then
	      raise MshiftException
	    else
	      (hd1 + delta)	     
	 )
	   , shift_var hd2 delta)::acc	  
      with
	| MshiftException -> acc
  ) s []
;;


let rec apply_substitution_term (te: term) (s: substitution) : term =
  match te with
    | Type n -> Type n
    | Cste n -> Cste n
    | Obj o -> Obj o
    | Var x -> (
	(List.fold_right 
	   (fun (hd1, hd2) acc ->
	      if (hd1 = x) then 		
		hd2
	      else 
		acc
	   ) 
	) s (Var x)
      )
    | Let (n, t1, t2) -> (
	let t1' = apply_substitution_term t1 s in
	let s' = shift_var_substitution s 1 in
	let t2' = apply_substitution_term t2 s' in
	  Let (n, t1', t2')
      )	
    | Lambda ((x, t1, n), t2) -> (
	let t1' = apply_substitution_term t1 s in
	let s' = shift_var_substitution s 1 in
	let t2' = apply_substitution_term t2 s' in
	  Lambda ((x, t1', n), t2')
      )
    | Forall ((x, t1, n), t2) -> (
	let t1' = apply_substitution_term t1 s in
	let s' = shift_var_substitution s 1 in
	let t2' = apply_substitution_term t2 s' in
	  Forall ((x, t1', n), t2')
      )
    | Phi (x, l, ty, terminaison, te) -> (
	let (s', l') = List.fold_left (
	  fun  (s', l') (x, te, n) ->
	    let s'' = shift_var_substitution s' 1 in
	    let te' = apply_substitution_term te s' in
	      (s'', l' @ (x, te', n)::[])
	) (s, []) l in
	let ty' = apply_substitution_term ty s' in
	let s'' = shift_var_substitution s' 1 in
	let te' = apply_substitution_term te s'' in
	  Phi (x, l', ty', terminaison, te')
      )
    | Ind (x, l, ty, lcons) -> 	
	let (s', l') = List.fold_left (
	  fun  (s', l') (x, te, n) ->
	    let s'' = shift_var_substitution s' 1 in
	    let te' = apply_substitution_term te s' in
	      (s'', l' @ (x, te', n)::[])
	) (s, []) l in
	let ty' = apply_substitution_term ty s' in
	let s'' = shift_var_substitution s' 1 in
	let lcons' = List.map (fun hd -> apply_substitution_term hd s'') lcons in
	  Ind (x, l', ty', lcons')

    | Constr (n, te) -> Constr (n, apply_substitution_term te s)
    | Match (te, ldes, ret) -> 
	Match (apply_substitution_term te s, 
	       apply_substitution_listdestructor ldes s, 
	       (apply_substitution_term ret s)
	      )
    | App l -> App (List.map (fun (hd1, hd2) -> (apply_substitution_term hd1 s, hd2)) l)
and apply_substitution_listterm (lte: term list) (s: substitution) =
  List.map (fun hd -> apply_substitution_term hd s) lte  
and apply_substitution_listdestructor (ldes: (term * term) list) (s: substitution) =
  List.map (fun hd -> let s = (List.fold_right (fun (hd1, hd2) acc ->
						  if (hd1 < 0 && fvsin hd1 (fv (fst hd))) then
						    acc
						  else
						    (hd1, hd2)::acc
					       ) s []
			      ) in
	      (apply_substitution_term (fst hd) s, apply_substitution_term (snd hd) s) 
	   ) ldes
;;

let rec compose_substitution (s: substitution) : substitution =
  let s' = List.rev s in
  let s'' = apply_substitution_substitution s' in
    List.rev s''
and apply_substitution_substitution (s: substitution) : substitution =
    match s with
      | [] -> []
      | hd::tl -> 
	  let tl' = List.map (fun (hd1, hd2) -> (hd1, apply_substitution_term hd2 (hd::[]))) tl in
	  let tl'' = apply_substitution_substitution tl' in
	    hd::tl''    
;;



exception UnificationFail of int list
;;

exception UnificationUnknown
;;

(* level correspond to the level of quantified variable *)
let rec unification_term (t1: term) (t2: term) (def: (term * term * defnature) objdef) : (substitution * univ_level_constraint list) =
    try (
      match (t1, t2) with
	| (Type alpha, Type beta) -> 
	    if (alpha = beta) then
	      ([], [])
	    else
	      ([] , (UEq (alpha, beta))::[])
	| (Cste c1, Cste c2) -> (
	    if (c1 = c2) then
	      ([], [])
	    else
	      raise (UnificationFail [])
	  )
	| (Obj o1, Obj o2) -> (
	    if (o1#equal o2) then
	      ([], [])
	    else
	      raise (UnificationFail [])
	  )
	| (Var x1, Var x2) -> (
	    match (x1 < 0, x2 < 0) with
	      | (false, false) -> (
		  if (x1 = x2) then
		    ([], [])
		  else
		    raise (UnificationFail [])
		)
	      | (true, _) -> (
		  
		    ((x1, t2)::[], [])
		  
		)
	      | (_, true) -> (
		  
		    ((x2, t1)::[], [])
		  
		)
	  )

	| (Var x1, t2) -> (

	    if (x1 >= 0) then 
	      raise (UnificationFail (x1::[]))
	    else (
	      let fv2 = fv t2 in
		if (fvsin x1 fv2) then
		  raise (UnificationFail [])
		else
		  ((x1, t2)::[], [])
	    )
	  )

	| (t1, Var x2) -> (

	    if (x2 >= 0) then 
	      raise (UnificationFail (x2::[]))
	    else (
	      let fv1 = fv t1 in
		if (fvsin x2 fv1) then
		  raise (UnificationFail [])
		else
 		  ((x2, t1)::[], [])
	    )
	  )

	| (Let (x1, t11, t12), Let (x2, t21, t22)) -> (

	    let (s1, c1) = unification_term t11 t21 def in
	    let s1' = shift_var_substitution s1 1 in
	    let t12' = apply_substitution_term t12 s1' in
	    let t22' = apply_substitution_term t22 s1' in
	    let (s2, c2) = unification_term t12' t22' def in
	    let s2' = shift_var_substitution s2 (-1) in
	      (compose_substitution (s1 @ s2'), c1 @ c2)

	  )
	| (Lambda ((x1, t11, n1), t12), Lambda ((x2, t21, n2), t22)) -> (

	    if (not (n1 = n2)) then
	      raise (UnificationFail [])
	    else (

	      let (s1, c1) = unification_term t11 t21 def in
	      let s1' = shift_var_substitution s1 1 in
	      let t12' = apply_substitution_term t12 s1' in
	      let t22' = apply_substitution_term t22 s1' in
	      let (s2, c2) = unification_term t12' t22' def in
	      let s2' = shift_var_substitution s2 (-1) in
		(compose_substitution (s1 @ s2'), c1 @ c2)

	    )
	  )
	| (Forall ((x1, t11, n1), t12), Forall ((x2, t21, n2), t22)) -> (

	    if (not (n1 = n2)) then
	      raise (UnificationFail [])
	    else (

	      let (s1, c1) = unification_term t11 t21 def in
	      let s1' = shift_var_substitution s1 1 in
	      let t12' = apply_substitution_term t12 s1' in
	      let t22' = apply_substitution_term t22 s1' in
	      let (s2, c2) = unification_term t12' t22' def in
	      let s2' = shift_var_substitution s2 (-1) in
		(compose_substitution (s1 @ s2'), c1 @ c2)

	    )
	  )
	| (Phi (x1, l1, ty1, _, body1), Phi (x2, l2, ty2, _, body2)) -> (
	    let (s, c) = unification_listvarterm l1 l2 def in
	    let (ty1', ty2') = (apply_substitution_term ty1 s, apply_substitution_term ty2 s) in
	    let s' = shift_var_substitution s 1 in 
	    let (body1, body2) = (apply_substitution_term body1 s', apply_substitution_term body2 s') in
	    let (s1, c1) = unification_term ty1' ty2' def in
	    let s1' = shift_var_substitution s1 1 in 
	    let (body1, body2) = (apply_substitution_term body1 s1', apply_substitution_term body2 s1') in
	    let (s2, c2) = unification_term body1 body2 def in
	      (compose_substitution (
		 shift_var_substitution (s @ s1 @ (shift_var_substitution s2 (-1))) (List.length l1)
	       ), c @ c1 @ c2)
	  )

	| (Ind (x1, l1, ty1, lcons1), Ind (x2, l2, ty2, lcons2)) -> (
	    let (s, c) = unification_listvarterm l1 l2 def in
	    let (ty1', ty2') = (apply_substitution_term ty1 s, apply_substitution_term ty2 s) in
	    let s' = shift_var_substitution s 1 in 
	    let (lcons1, lcons2) = (apply_substitution_listterm lcons1 s', apply_substitution_listterm lcons2 s') in
	    let (s1, c1) = unification_term ty1' ty2' def in
	    let s1' = shift_var_substitution s1 1 in 
	    let (lcons1, lcons2) = (apply_substitution_listterm lcons1 s1', apply_substitution_listterm lcons2 s1') in
	    let (s2, c2) = unification_listterm lcons1 lcons2 def in
	      (compose_substitution (
		 shift_var_substitution (s @ s1 @ (shift_var_substitution s2 (-1))) (List.length l1)
	       ), c @ c1 @ c2)
	  )

	| (App l1, App l2) -> (
	    if (List.length l1 <> List.length l2) then
	      raise (UnificationFail [])
	    else (
	      let (l11, l12) = List.split l1 in
	      let (l21, l22) = List.split l2 in
		if (l12 <> l22) then
		  raise (UnificationFail [])
		else (
		  unification_listterm l11 l21 def
		)
	    )
	  )

	| (Match (t1, l1, ret1), Match (t2, l2, ret2)) -> (
	    let (s, c) = unification_term t1 t2 def in
	    let l1' = apply_substitution_listdestructor l1 s in
	    let l2' = apply_substitution_listdestructor l2 s in
	    let (s', c') = unification_listdestruct l1' l2' def in
	    let s'' = compose_substitution (s @ s') in
	    let ret1 = apply_substitution_term ret1 s'' in
	    let ret2 = apply_substitution_term ret2 s'' in
	    let (s''', c''' ) = unification_term ret1 ret2 def
	    in
	      (compose_substitution (
		 s'' @ s'''
	       ), c @ c' @ c''')
	  )

	| (Constr (n1, t1), Constr (n2, t2)) -> (
	    if (n1 <> n1) then
	      raise (UnificationFail [])
	    else
	      unification_term t1 t2 def
	  )

	| _ -> (
	    (*
	    printf "Unification Case Not Yet Implemented\n";
	    pprintterm t1 true;
	    printf "Vs\n";
	    pprintterm t2 true;
	    printf "\n";
	    *)
	    raise (UnificationFail [])
	  )

    ) with
      | UnificationFail l -> (
	  (* in this case look if we could try 
	     a beta reduction/eta expension 
	  *)

	  (* this function return None if the term cannot be betared
	     else we return a Some of the betareded term
	  *)
	  
	  let dobetared te = (
	    let te' = betared te def in
	      if (te' = te) then None else Some te'		
	  ) in
	    match (dobetared t1, dobetared t2) with
	      | (None, None) -> (
		  (*
		  printf "Unification Failed\n";
		  pprintterm t1 true;
		  printf "Vs\n";
		  pprintterm t2 true;
		  printf "\n";
		  *)
		  raise (UnificationFail l)
		)
	      | (Some t1, None) -> unification_term t1 t2 def
	      | (None, Some t2) -> unification_term t1 t2 def
	      | (Some t1, Some t2) -> unification_term t1 t2 def

	)
      | UnificationUnknown ->
	  raise UnificationUnknown
      | MshiftException ->
	  (*
	  printf "Unification Failed: Shifting problem\n";
	  pprintterm t1 true;
	  printf "Vs\n";
	  pprintterm t2 true;
	  printf "\n";
	  *)
	  raise (UnificationFail [])

and unification_listvarterm (l1: (name * term * nature) list) (l2: (name * term * nature) list) (def: (term * term * defnature) objdef) : (substitution * univ_level_constraint list) =
  match (l1, l2) with
    | ([], []) -> ([], [])
    | ((_, hd1, _)::tl1, (_, hd2, _)::tl2) -> (
	let (s, c) = unification_term hd1 hd2 def in

	let (_, tl1') = List.fold_left (
	  fun  (s', l') (x, te, n) ->
	    let s'' = shift_var_substitution s' 1 in
	    let te' = apply_substitution_term te s' in
	      (s'', l' @ (x, te', n)::[])
	) (s, []) tl1 in

	let (_, tl2') = List.fold_left (
	  fun  (s', l') (x, te, n) ->
	    let s'' = shift_var_substitution s' 1 in
	    let te' = apply_substitution_term te s' in
	      (s'', l' @ (x, te', n)::[])
	) (s, []) tl2 in

	let (s', c') = unification_listvarterm tl1' tl2' def in

	  (compose_substitution (
	     (shift_var_substitution s (List.length tl1)) @ s'
	   ), c @ c')	  
	  
      ) 
    | _ -> raise (UnificationFail [])
and unification_listterm (l1: term list) (l2: term list) (def: (term * term * defnature) objdef) : (substitution * univ_level_constraint list) =
  match (l1, l2) with
    | ([], []) -> ([], [])
    | (hd1::tl1, hd2::tl2) -> (

	let (s, c) = unification_term hd1 hd2 def in
	let tl1' = List.map (fun hd -> apply_substitution_term hd s) tl1 in
	let tl2' = List.map (fun hd -> apply_substitution_term hd s) tl2 in
	let (s', c') = unification_listterm tl1' tl2' def in
	  (compose_substitution (
	     (shift_var_substitution s (List.length tl1)) @ s'
	   ), c @ c')	  
	  
      ) 
    | _ -> raise (UnificationFail [])
and unification_listdestruct (l1: (term * term) list) (l2: (term * term) list) (def: (term * term * defnature) objdef) : (substitution * univ_level_constraint list) =
  match (l1, l2) with
    | ([], []) -> ([], [])
    | (hd1::tl1, hd2::tl2) -> (

	let (s, c) = unification_term (fst hd1) (fst hd2) def in
	let (res1, res2) = (apply_substitution_term (snd hd1) s, apply_substitution_term (snd hd2) s) in
	let (s1, c1) = unification_term res1 res2 def in
	let s = compose_substitution (s @ s1) in
	let tl1' = apply_substitution_listdestructor tl1 s in
	let tl2' = apply_substitution_listdestructor tl2 s in
	let (s', c') = unification_listdestruct tl1' tl2' def in
	  (compose_substitution (
	     (shift_var_substitution s (List.length tl1)) @ s'
	   ), c @ c' @ c1)	  
	  
      ) 
    | _ -> raise (UnificationFail [])

(* beta reduction/eta expansion, lazy *)	  
and betared t (def: (term * term * defnature) objdef) =
  match t with
    | Type n -> Type n
    | Cste n -> Cste n
    | Obj o -> Obj o
    | Var x -> Var x
    | Let (n, t1, t2) -> (
	let t1' = betared t1 def in
	let s = (0, shift_var t1' 1)::[] in
	let t2' = apply_substitution_term t2 s in
	  betared (shift_var t2' (-1)) def
      )	
    | Lambda ((x, t1, n), t2) -> (
	let t1' = betared t1 def in
	  Lambda ((x, t1', n), t2)
      )
    | Forall ((x, t1, n), t2) -> (
	let t1' = betared t1 def in
	  Forall ((x, t1', n), t2)
      )
    | Phi (x, l, ty, terminaison, te) -> (
	t
      )
    | Ind (x, l, ty, lcons) -> (	
	t
      )
    | Constr (n, te) -> (
	t
      )
    | Match (te, ldes, ret) -> (
	let te' = betared te def in
	let res = List.fold_left (
	  fun acc hd ->
	    match acc with
	      | Some te -> Some te
	      | None ->
		  match unification (fst hd) te' def with
		    | Mgu (s, _) -> Some (apply_substitution_term (snd hd) s)
		    | _ -> None
	) None ldes in
	  match res with
	    | None -> Match (te', ldes, ret)
	    | Some te -> betared te def
      )
    | App l -> (
	match l with
	  | [] -> raise (Failure "Catastrophic: Empty Apply")
	  | (hd, _) :: [] -> betared hd def
	  | (te, b) :: (hd, b') :: tl -> (
	      let te' = betared te def in
		match te' with
		  | Cste c -> (
		      match finddef c def with
			| None -> raise (Failure "Catastrophic: No such Cste")
			| Some (n , (te, ty, nature)) -> 
			    match nature with
			      | DataDef -> t
			      | TypeDef -> t
			      | _ -> betared (App ((te, b)::(hd, b')::tl)) def				  
		    ) 
		  | Lambda ((_, t1, _), t2) -> (
			let s = (0, shift_var hd 1)::[] in
			let t2' = apply_substitution_term t2 s in
			  betared (App ((shift_var t2' (-1), b)::tl)) def
		    )
		  | Phi (x, l, ty, terminaison, te) -> (
		      if (1 + List.length tl = List.length l) then ( 

			let s = (0, Phi (x, l, ty, terminaison, te))::[] in
			let te' = apply_substitution_term te s in
			  betared (App ((List.fold_right (fun hd acc ->
							    Lambda (hd, acc)
							 ) l (shift_var te' (-1))
					, b) :: (hd, b') :: tl
				       )
				  ) def				     
		      ) else t
		    )
		  | App l' ->
		      betared (App (l' @ (hd, b') :: tl)) def
		  | _ -> t
	    )
      )
(* level correspond to the level of quantified variable *)
and unification (t1: term) (t2: term) (def: (term * term * defnature) objdef) : unification =
    try (
      let (s, c) = unification_term t1 t2 def in
	Mgu (s, c)
    ) with
      | UnificationUnknown -> DnkMgu
      | UnificationFail l -> NoMgu l
;;

