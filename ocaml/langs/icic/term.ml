open Universe;;
open Pprinter;;
open Parser;;
open Array;;
open Output;;
open String;;
open Listext;;
open Array;;
open Definition;;
open Printf;;
open Varmap;;

let ($) f x = f x;;

type name = string
;;

type defnature =
  | DataDef
  | FunctionDef
  | TypeDef
  | UnknownDef
;;

type nature =
  | Implicite
  | Explicite
  | Hidden
;;

type terminaison_pattern =
    Nothing
;;

class virtual ['a] primitive =
object 
  method virtual get_name: string
  method virtual get_type: 'a
  method virtual equal: 'a primitive -> bool
  method virtual pprint: 'a list -> token list
(*  method virtual exec: 'a list -> ('a * 'a * defnature) objdef -> 'a*)
  method virtual show: token
  method virtual uuid: (float * float * float)
end;;


type term =
    | TType of univ_level
    | TCste of name
    | TPrim of term primitive
    | TVar of int
    | TLet of ((name * term * term) * term)
    | TLambda of binder * term
    | TForall of binder * term
    | TPhi of name * binders * term * terminaison_pattern * term
    | TInd of name * binders * term * term array	

    (* bool is the true if the application is implicit *)
    | TApp of term * (term * nature) list
	
    (* term to destruct, list of destructors, returned type, destruct inductive type *)	
    | TMatch of term * (term option) array * term
	
    | TConstr of int * term
	
and binder = (name * term * nature)
and binders = binder list
;;


(* helper functions *)

let term_head_string (t: term) : string =
  match t with
    | TType _ ->  "TType"
    | TCste _ -> "TCste"
    | TPrim _ -> "TPrim"
    | TVar _ -> "TVar"
    | TLet _ -> "TLet"
    | TLambda _ -> "TLambda"
    | TForall _ -> "TForall"
    | TPhi _ -> "TPhi"
    | TInd _ -> "TInd"
    | TApp _ -> "TApp"
    | TMatch _ -> "TMatch"
    | TConstr _ -> "TConstr"
;;

let not_supported_case (s: string) (t: term) : string =
  (String.concat "" [s; ", term not supported: "; term_head_string t])
;;

let rec normalize (t: term) =
  match t with
    | TApp (TApp (te, l), l') -> normalize (TApp (te, l @ l'))
    | _ -> t
;;

(* Pretty printing *)
let rec containsqv (t:term) (v: int) : bool =
  match t with
    | TType n -> false
    | TCste n -> false
    | TPrim o -> false
    | TVar x -> (x = v)
    | TLet ((n, t1, ty), t2) -> (
	if (containsqv t1 v) then true
	else if (containsqv ty v) then true
	else containsqv t2 (v+1)
      )	
    | TLambda ((x, t1, n), t2) -> (
	if (containsqv t1 v) then true
	else containsqv t2 (v+1)
      )
    | TForall ((x, t1, n), t2) -> (
	if (containsqv t1 v) then true
	else containsqv t2 (v+1)
      )
    | TApp (fct, l) -> List.fold_left (fun acc hd -> if acc then acc else (containsqv (fst hd) v)) (containsqv fct v) l
    | TPhi (x, l, ty, terminaison, te) -> (
	false
      )
    | TInd (x, l, ty, lcons) -> (
	false
      )
    | TConstr (n, te) -> (
	false
      )
    | TMatch (te, ldes, ret) -> (
	false
      )
    | _ -> raise (Failure "containsqv: case not supported")
;;

let rec term2token (t: term) (show_univ: bool) (lv: string list): token list =
  match t with
    | TType ul -> (Verbatim "Type") :: if show_univ then (Verbatim "(") :: (univ_level2token ul) @ (Verbatim ")") :: [] else []
    | TCste c -> [Verbatim ""; Verbatim c; Verbatim ""]
    | TPrim p -> p#show::[]
    | TVar i -> 
	if (i >= 0) then (
	  try 
	    (Verbatim (List.nth lv i)) :: []
	  with
	    | _ -> (Verbatim "<") :: (Verbatim (string_of_int i)) :: (Verbatim ">") :: []
	)
	else
	  (Verbatim "?") :: (Verbatim (string_of_int i)) :: []

    | TLet ((n, te1, ty), te2) ->
	let t1 = Box (term2token te1 show_univ lv) in
	let ty = Box (term2token ty show_univ lv) in
	let t2 = Box (term2token te2 show_univ (n::lv)) in
	  [Verbatim "let"; Space 1; Verbatim n; Space 1; Verbatim "="; Space 1; t1; Space 1; Verbatim ":"; Space 1; ty; Space 1; Verbatim "in"; Space 1; t2]

    | TLambda ((v, t1, n), t2) -> (
	
	let t1 = Box (term2token t1 show_univ lv) in
	let t2 = Box (term2token t2 show_univ (v::lv)) in
	let (a, b) = 
	  match n with
	    | Implicite -> (Verbatim "[", (Verbatim "] ->"))
	    | Explicite -> (Verbatim "(", (Verbatim ") ->"))
	    | Hidden -> (Verbatim "{", (Verbatim "} ->"))
	in
	  ((Verbatim "\\") :: (Space 1) :: a ::(Verbatim v) :: (Verbatim ":") :: (Space 1) :: t1 :: b :: (Space 1) :: t2 :: [])
      )

    | TForall ((v, t1, n), t2) -> (
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

    | TInd(x, largs, ty, lcons) -> 
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
	  (Array.fold_left (fun acc hd ->
			     acc @ Box (
			       (Verbatim "|") :: (Space 1) :: (term2token hd show_univ (x :: (List.rev (List.map (fun (x, ty, n) -> x) largs)) @ lv))
			     ) :: Newline :: []
			  ) [] lcons  
	  )

    | TPhi(x, largs, ty, _, body) -> 
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

    | TConstr (n, te) -> (Verbatim "Constr") :: (Space 1) :: (Verbatim (string_of_int n)) :: (Space 1) :: (Verbatim "of") :: (Space 1) :: (term2token te show_univ lv)

    | TApp (fct, l) -> (Verbatim "(") :: (term2token fct show_univ lv) @ (Verbatim ")") ::
	(List.fold_left (fun acc hd -> 
			   let (l, r) = match snd hd with
			     | Implicite -> (Verbatim "[", (Verbatim "]"))
			     | Explicite -> (Verbatim "(", (Verbatim ")"))
			     | Hidden -> (Verbatim "{", (Verbatim "}"))
			   in
			     acc @ (Space 1) :: l :: (term2token (fst hd) show_univ lv) @ r :: []
			) [] l)

    | TMatch (te, ldes, ret) -> (
	(Verbatim "match") :: (Space 1) :: (term2token te show_univ lv) @ (Space 1) :: (Verbatim "with") ::
	  (List.concat (
	     List.map (
	       fun hd ->
		 match hd with
		   | Some hd ->
		       Newline :: (Verbatim "|") :: (Space 1) :: (term2token hd show_univ lv)
		   | _ -> []
	     ) (Array.to_list ldes)
	   )
	  )
      )

    | _ -> raise (Failure (not_supported_case "term2token" t))
;;

(*********************)

module OrderedFreeVar = 
    struct
      type t = int
      let compare (x: int) (y: int) = (x - y)
    end;;

module FreeVarSet = Set.Make(OrderedFreeVar);; 
module FreeVarMap = Map.Make(OrderedFreeVar);; 

let fvsin e s = FreeVarSet.subset (FreeVarSet.singleton e) s;;

(* TODO: redo to have also qv that appears free *)
let rec fv (te: term) (level: int) : FreeVarSet.t =
  match te with
    | TType n -> FreeVarSet.empty
    | TCste n -> FreeVarSet.empty
    | TVar x -> 
	if (x < 0) then 
	  FreeVarSet.singleton x 
	else 
	  if x >= level then
	    FreeVarSet.singleton (x - level)
	  else
	    FreeVarSet.empty
    | TPrim p -> FreeVarSet.empty
    | TLet ((n, t1, ty), t2) -> FreeVarSet.union (FreeVarSet.union (fv t1 level) (fv ty level)) (fv t2 level)
    | TLambda ((x, t1, n), t2) -> FreeVarSet.union (fv t1 level) (fv t2 level)
    | TForall ((x, t1, n), t2) -> FreeVarSet.union (fv t1 level) (fv t2 level)
    | TPhi (x, l, ty, terminaison, te) -> 
	FreeVarSet.union 
	  (snd $ List.fold_right (
	     fun (_, te, _) (level, acc) ->
	       (level+1, FreeVarSet.union (fv te level) acc)
	   ) l (level, FreeVarSet.empty)
	  )
	  (FreeVarSet.union (fv ty (level + List.length l)) (fv te (1 + level + List.length l)))
    | TInd (x, l, ty, lcons) -> 
	FreeVarSet.union 
	  (snd $ List.fold_right (
	     fun (_, te, _) (level, acc) ->
	       (level+1, FreeVarSet.union (fv te level) acc)
	   ) l (level, FreeVarSet.empty)
	  )
	  (FreeVarSet.union (fv ty (level + List.length l)) (
	     (Array.fold_right (
		fun hd acc ->
		  FreeVarSet.union (fv hd (1 + level + List.length l)) acc
	      ) lcons FreeVarSet.empty 
	     ) 
	   )
	  )
    | TConstr (n, te) -> fv te level
    | TMatch (te, ldes, ret) -> 
	FreeVarSet.union
	  (fv te level)
	  (FreeVarSet.union
	     (
	       (Array.fold_right (
		  fun hd acc ->
		    FreeVarSet.union (match hd with
					| None -> FreeVarSet.empty
					| Some hd -> fv hd level
				     ) acc
		) ldes FreeVarSet.empty 
	       )  
	     )
	     (fv ret level)
	  )
    | TApp (fct, l) -> 
	FreeVarSet.union
	  (fv fct level)
	  (List.fold_right (
	     fun (hd, _) acc ->
	       FreeVarSet.union (fv hd level) acc
	   ) l FreeVarSet.empty 
	  )  
;;



(* shift_var_term *)

exception MshiftException;;

(* shift of quantified-free variables *)

let rec shift_var (te: term) (delta: int) : term =
  shift_var_term te 0 delta
and shift_var_term (te: term) (level: int) (delta: int) : term =
  match te with
    | TType n -> TType n
    | TCste n -> TCste n
    | TVar x -> (
	if (x < 0) then TVar x
	else 
	  if (x >= level) then (
	    if (x + delta < level) then
	      raise MshiftException
	    else
	      TVar (x + delta)
	  ) else 
	    TVar x     
      )
    | TPrim p -> TPrim p

    | TLet ((n, t1, ty), t2) ->
	TLet ((n, shift_var_term t1 level delta, shift_var_term ty level delta), shift_var_term t2 (level + 1) delta)

    | TLambda ((x, t1, n), t2) ->
	TLambda ((x, shift_var_term t1 level delta, n), shift_var_term t2 (level + 1) delta)

    | TForall ((x, t1, n), t2) ->
	TForall ((x, shift_var_term t1 level delta, n), shift_var_term t2 (level + 1) delta)

    | TPhi (n, bs, ty, tp, body) ->
	TPhi (n, 
	      shift_var_binders bs level delta, 
	      shift_var_term ty (List.length bs + level) delta, 
	      tp, 
	      shift_var_term body (List.length bs + level + 1) delta
	     )

    | TInd (n, bs, ty, cs) ->
	TInd (n,
	      shift_var_binders bs level delta, 
	      shift_var_term ty (List.length bs + level) delta,
	      (Array.map (fun hd -> shift_var_term hd (List.length bs + level + 1) delta) cs)
	     )

    | TApp (fct, args) ->
	TApp (shift_var_term fct level delta,
	      List.map (fun (hd1, hd2) -> (shift_var_term hd1 level delta, hd2)) args
	     )
	
    (* term to destruct, list of destructors, returned type, destruct inductive type *)	
    | TMatch (te, ldes, ret) ->
	TMatch (shift_var_term te level delta,
		Array.map (fun hd -> (match hd with
					| None -> None
					| Some hd -> Some (shift_var_term hd level delta)
				     )
			  ) ldes,
		(shift_var_term ret level delta)
	       )
	  
    | TConstr (i, ind) -> TConstr (i, shift_var_term ind level delta)

and shift_var_binders (bs: binders) level delta =
  List.map (
    fun ((hd1, hd2, hd3), hd4) ->
      (hd1, shift_var_term hd2 (hd4 + level) delta, hd3)
  ) (List.combine bs (iota 0 (List.length bs - 1)))
;;


(* extraction *)

(* change hidden in explicit *)
let rec hidden2explicite (te: term) =
  match te with
    | TForall ((x, ty, Hidden), te) ->
	TForall ((x, ty, Explicite), hidden2explicite te)
    | TForall ((x, ty, n), te) ->
	TForall ((x, ty, n), hidden2explicite te)
    | TLambda ((x, ty, Hidden), te) ->
	TLambda ((x, ty, Explicite), hidden2explicite te)
    | TLambda ((x, ty, n), te) ->
	TLambda ((x, ty, n), hidden2explicite te)
    | _ -> te
;;

(* extraction *)
let rec extract (te: term) : term =
  match te with
    | TType n -> TType n
    | TCste n -> TCste n
    | TVar x -> TVar x
    | TPrim p -> TPrim p
    | TLet ((n, t1, ty), t2) ->
	TLet ((n, extract t1, extract ty), extract t2)
    | TLambda ((x, t1, Implicite), t2) ->
	extract (shift_var t2 (-1))
    | TLambda ((x, t1, _), t2) ->
	TLambda ((x, TType Zero, Explicite), extract t2)
    | TForall ((x, t1, n), t2) ->
	TForall ((x, extract t1, n), extract t2)

    (* this is not tested ... 
       and I think not correct ...
    *)
    | TPhi (x, l, ty, terminaison, te) ->
	let (_, l', te) = fold_left2 (
	  fun (acc1, acc2, acc3) (hd1, hd2, hd3) tl ->
	    if (hd3 = Implicite) then (
	      
	      ((acc1 - 1, ((hd1, extract hd2, hd3)::acc2), shift_var_term acc3 acc1 (-1)), 
	       List.map (
		 fun ((hd1, hd2, hd3), hd4) ->
		   (hd1, shift_var_term hd2 hd4 (-1), hd3)
	       ) (List.combine tl (iota acc1 (acc1 + List.length tl - 1)))
	      )

	    ) else 
	      ((acc1 - 1, ((hd1, extract hd2, hd3)::acc2), acc3), tl)
	      
	) (List.length l + 1, [], te) l in
	  TPhi (x, l', extract ty, terminaison, extract te)

    | TInd (x, l, ty, lcons) ->
	let (_, l', te) = fold_left2 (
	  fun (acc1, acc2, acc3) (hd1, hd2, hd3) tl ->
	    if (hd3 = Implicite) then (
	      
	      ((acc1 - 1, ((hd1, extract hd2, hd3)::acc2), shift_var_term acc3 acc1 (-1)), 
	       List.map (
		 fun ((hd1, hd2, hd3), hd4) ->
		   (hd1, shift_var_term hd2 hd4 (-1), hd3)
	       ) (List.combine tl (iota acc1 (acc1 + List.length tl - 1)))
	      )

	    ) else 
	      ((acc1 - 1, ((hd1, extract hd2, hd3)::acc2), acc3), tl)
	      
	) (List.length l + 1, [], te) l in
	let lcons' = (Array.map extract lcons) in
	  TInd (x, l', extract ty, lcons')
    | TConstr (n, te) -> TConstr (n, extract te)
    | TMatch (te, ldes, ret) ->
	let ldes' = Array.map (fun hd -> (match hd with
					    | None -> None
					    | Some hd -> Some (extract hd)
					 ) 
			      ) ldes in
	  TMatch (extract te, ldes', (extract ret))
    | TApp (fct, l) ->
	TApp (extract fct,
	      List.fold_right (fun (hd1, hd2) acc -> 
				 if hd2 = Implicite then
				   acc
				 else
				   (hd1, hd2)::acc
			      ) l []
	     )
;;

(* substitution and unification datatype *)

type substitution = term FreeVarMap.t
;;

(* shift_var substitution *)

(*
val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
*)

let shift_var_substitution_err (s: substitution) (delta: int) : (substitution * substitution) =
  FreeVarMap.fold (
    fun key value (acc1, acc2) ->
      try 
	let key' = (if (key < 0) then key
		    else 
		      if (key + delta < 0) then
			raise MshiftException
		      else
			(key + delta)	     
		   ) in
	let value' = shift_var value delta in
	  (FreeVarMap.add key' value' acc1, acc2)
      with
	| MshiftException -> (acc1, FreeVarMap.add key value acc2)
  ) s (FreeVarMap.empty, FreeVarMap.empty)
;;

let shift_var_substitution (s: substitution) (delta: int) : substitution =
  fst $ shift_var_substitution_err s delta
;;


(* apply_substitution_term *)

let rec apply_substitution_term (te: term) (s: substitution) : term =
  match te with
    | TType n -> TType n
    | TCste n -> TCste n
    | TPrim p -> TPrim p
    | TVar x -> (
	try
	  FreeVarMap.find x s
	with
	  | Not_found -> TVar x
      )
    | TLet ((n, t1, ty), t2) -> (
	let t1' = apply_substitution_term t1 s in
	let ty' = apply_substitution_term ty s in
	let s' = shift_var_substitution s 1 in
	let t2' = apply_substitution_term t2 s' in
	  TLet ((n, t1', ty'), t2')
      )	
    | TLambda ((x, t1, n), t2) -> (
	let t1' = apply_substitution_term t1 s in
	let s' = shift_var_substitution s 1 in
	let t2' = apply_substitution_term t2 s' in
	  TLambda ((x, t1', n), t2')
      )
    | TForall ((x, t1, n), t2) -> (
	let t1' = apply_substitution_term t1 s in
	let s' = shift_var_substitution s 1 in
	let t2' = apply_substitution_term t2 s' in
	  TForall ((x, t1', n), t2')
      )
    | TPhi (x, l, ty, terminaison, te) -> (
	let (s', l') = List.fold_left (
	  fun  (s', l') (x, te, n) ->
	    let s'' = shift_var_substitution s' 1 in
	    let te' = apply_substitution_term te s' in
	      (s'', l' @ (x, te', n)::[])
	) (s, []) l in
	let ty' = apply_substitution_term ty s' in
	let s'' = shift_var_substitution s' 1 in
	let te' = apply_substitution_term te s'' in
	  TPhi (x, l', ty', terminaison, te')
      )
    | TInd (x, l, ty, lcons) -> 	
	let (s', l') = List.fold_left (
	  fun  (s', l') (x, te, n) ->
	    let s'' = shift_var_substitution s' 1 in
	    let te' = apply_substitution_term te s' in
	      (s'', l' @ (x, te', n)::[])
	) (s, []) l in
	let ty' = apply_substitution_term ty s' in
	let s'' = shift_var_substitution s' 1 in
	let lcons' = (Array.map (fun hd -> apply_substitution_term hd s'') lcons) in
	  TInd (x, l', ty', lcons')

    | TConstr (n, te) -> TConstr (n, apply_substitution_term te s)
    | TMatch (te, ldes, ret) -> 
	TMatch (apply_substitution_term te s, 
		apply_substitution_listdestructor ldes s, 
		(apply_substitution_term ret s)
	       )
    | TApp (fct, l) -> 
	TApp (apply_substitution_term fct s,
	      List.map (fun (hd1, hd2) -> (apply_substitution_term hd1 s, hd2)) l
	     )

and apply_substitution_listterm (lte: term list) (s: substitution) =
  List.map (fun hd -> apply_substitution_term hd s) lte  
and apply_substitution_listdestructor (ldes: (term option) array) (s: substitution) =
  Array.map (fun hd -> 
	       match hd with
		 | None -> None
		 | Some hd -> Some (apply_substitution_term hd s)
	    ) ldes
;;

(* compose substitution *)

let rec addsubstitution (v: int) (t: term) (s: substitution): substitution =
  FreeVarMap.add v t (
    FreeVarMap.map (fun t -> apply_substitution_term t (FreeVarMap.add v t FreeVarMap.empty)) s
  )
;;

let compose_substitution (s1: substitution) (s2: substitution): substitution =
  FreeVarMap.fold addsubstitution s2 s1
;;

let pprintterm t show_univ =
  let t = term2token t show_univ [] in
  let t = Box t in
  let b = token2box t 80 2 in
    printbox b
;;

(* hepler functions *)
let rec decomp_forall (t: term) : binders * term =
  match t with
    | TForall (b, t) -> (
	let (bs, t) = decomp_forall t in
	  (b::bs, t)
      )
    | _ -> ([], t)
;;

let comp_forall (bs: binders) (body: term) : term =
  List.fold_right (fun hd acc -> TForall (hd, acc)) bs body
;;

let rec decomp_lambda (t: term) : binders * term =
  match t with
    | TLambda (b, t) -> (
	let (bs, t) = decomp_lambda t in
	  (b::bs, t)
      )
    | _ -> ([], t)
;;

let comp_lambda (bs: binders) (body: term) : term =
  List.fold_right (fun hd acc -> TLambda (hd, acc)) bs body
;;
