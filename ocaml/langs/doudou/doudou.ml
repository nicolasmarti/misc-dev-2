(* for parsing *)
open Parser
(* for pretty printing *)
open Pprinter

open Printf


(*********************************)
(* Definitions of data structure *)
(*********************************)

type name = string

type op = NoFix
	  | Prefix of int
	  | Infix of int * associativity
	  | Postfix of int

type symbol = | Name of name
	      | Symbol of name * op

type index = int

type nature = Explicit
	      | Implicit

class virtual ['a] tObj =
object 
  method uuid: int = 0
  method virtual get_name: string
  method virtual get_type: 'a
  method virtual pprint: unit -> token
  method virtual apply: ('a * nature) list -> 'a
end

type term = Type
	    | Cste of symbol
	    | Obj of term tObj

	    (* the Left name is only valid after parsing, and removed by typecheck*)
	    | TVar of index
		
	    (* these constructors are only valide after parsing, and removed by typechecking *)
	    | AVar
	    | TName of name

	    | App of term * (term * nature) list
	    | Impl of (symbol * term * nature) * term
	    | DestructWith of equation list

	    | TyAnnotation of term * term
	    | SrcInfo of pos * term

and equation = (pattern * nature) * term

and pattern = PType
	      | PVar of name * term
	      | PAVar of term
	      | PCste of symbol
	      | PAlias of name * pattern * term
	      | PApp of symbol * (pattern * nature) list * term

(* context of a term *)
type frame = {
  (* the symbol of the frame *)
  symbol : symbol;
  (* its type *)
  ty: term;

  (* its value: most stupid one: itself *)
  value: term;
    
  (* the free variables 
     fst: the type of the free variable
     snd: its corresponding value (by unification)
  *)
  fvs: (term * term) list;

  (* the stacks *)
  termstack: term list;
  naturestack: nature list;
  equationstack: equation list;
  patternstack: pattern list;
  
}

type context = frame list

let empty_context = []
	   
(* definitions *)
type defs = {
  (* here we store all id in a string *)
  (* id -> (type * value) *)
  store : (string, (term * term)) Hashtbl.t;
  mutable hist : symbol list;
}

type doudou_error = NoSuchBVar of index * context
		    | NegativeIndexBVar of index
		    | Unshiftable_term of term * int * int

		    | ErrorPosPair of pos option * pos option * doudou_error
		    | ErrorPos of pos * doudou_error

		    | UnknownCste of symbol

		    | UnknownUnification of context * term * term
		    | NoUnification of context * term * term

exception DoudouException of doudou_error

(********************************************)
(* example of source that should be process *)
(********************************************)

let example = "
Bool :: Type
True :: Bool
False :: Bool

(||) :: Bool -> Bool -> Bool
(&&) :: Bool -> Bool -> Bool

True || _ := True
_ || True := True
False || False := False

False && _ := False
_ && False := False
True && True := True

List :: Type -> Type
[[]] :: {A :: Type} -> List A
(:) :: {A :: Type} -> A -> List A -> List A

String :: Type

plusType :: Type -> Type -> Type
(+) :: {A B :: Type} -> A -> B -> plusType A B

multType :: Type -> Type -> Type
(*) :: {A B :: Type} -> A -> B -> multType A B

plusType Bool Bool := Bool
(+) {Bool} {Bool} := (||)

multType Bool Bool := Bool
(+) {Bool} {Bool} := (&&)

String :: Type

List :: Type -> Type
[[]] :: {A :: Type} -> List A
(:) :: {A :: Type} -> A -> List A -> List A

(@) :: {A :: Type} -> List A -> List A
[] @ l := l
l @ [] := l
(hd:tl) @ l := hd:(tl @ [])

map :: {A B :: Type} -> (A -> B) -> List A -> List B
map f [] := []
map f (hd:tl) := (f hd):(map f tl)

plusType (List A) (List A) := List a
(+) {List A} {List A} := (@)

multType Type Type := Type
(,) :: {A B :: Type} -> A -> B -> A * B

multType (List A) (List B) := List (List (A * B))

_ * [] := []
[] * _ := []
(hd1:tl1) * l := (map ( x := (x, hd1)) l) : (tl1 * l)

foldl :: {A B :: Type} -> (B -> A -> B) -> B -> List A -> B
foldl f acc [] := acc
foldl f acc (hd:tl) := foldl f (f acc hd) tl

foldr :: {A B :: Type} -> (A -> B -> B) -> List A -> B -> B
foldr f [] acc := acc
foldr f (hd:tl) acc := f hd (foldr f tl acc)

Nat :: Type
O :: Nat
S :: Nat -> Nat

T :: Type -> Type -> Nat -> Type
T _ B O := B
T A B (S n) := A -> T A B n

depfold :: {A B :: Type} -> (f:: B -> A -> B) -> B -> (n :: Nat) -> T A B n
depfold f acc O := acc
depfold f acc (S n) := (x := depfold f (f acc x) n)

NatPlus :: Nat -> Nat -> Nat 
NatPlus O x := x
NatPlus x O := x
NatPlus (S x) y := S (NatPlus x y)

plusType Nat Nat := Nat
(+) {Nat] {Nat} := NatPlus

depfold {Nat} (+) O (S (S 0)) :?: 
(* :?: Nat -> Nat -> Nat *)
"



(******************)
(*      misc      *)
(******************)

(* take and drop as in haskell *)
let rec take (n: int) (l: 'a list) :'a list =
  match n with
    | 0 -> []
    | i when i < 0 -> raise (Invalid_argument "take")
    | _ -> 
      match l with
	| [] -> []
	| hd::tl -> hd::take (n-1) tl

let rec drop (n: int) (l: 'a list) :'a list =
  match n with
    | 0 -> l
    | i when i < 0 -> raise (Invalid_argument "drop")
    | _ -> 
      match l with
	| [] -> []
	| hd::tl -> drop (n-1) tl


(* some traverse fold without the reverse *)
let mapacc (f: 'b -> 'a -> ('c * 'b)) (acc: 'b) (l: 'a list) : 'c list * 'b =
  let acc = ref acc in
  (List.map (fun hd -> let (hd, acc') = f !acc hd in
		       acc := acc';
		       hd) l, !acc)

(* assert that pos1 contains pos2 *)
let pos_in (pos1: pos) (pos2: pos) : bool =
  let ((begin_line1, begin_col1), (end_line1, end_col1)) = pos1 in
  let ((begin_line2, begin_col2), (end_line2, end_col2)) = pos2 in
  (* the start of pos2 must be equal or after the start of pos1 *)
  ((begin_line2 > begin_line1) || (begin_line1 = begin_line2 && begin_col2 >= begin_col1))
  (* and the end of pos2 must be equal or before the end of pos 1*)
  && ((end_line2 < end_line1) || (end_line1 = end_line2 && end_col2 <= end_col1))

(* computation of free variable in a term *)
module IndexSet = Set.Make(
  struct
    type t = int
    let compare x y = compare x y
  end
);;

let rec fv_term (te: term) : IndexSet.t =
  match te with
    | Type | Cste _ | Obj _ -> IndexSet.empty
    | TVar i when i >= 0 -> IndexSet.empty
    | TVar i when i < 0 -> IndexSet.singleton i
    | AVar -> raise (Failure "fv_term catastrophic: AVar")
    | TName _ -> raise (Failure "fv_term catastrophic: TName")
    | App (te, args) ->
      List.fold_left (fun acc (te, _) -> IndexSet.union acc (fv_term te)) (fv_term te) args
    | Impl ((s, ty, n), te) ->
      IndexSet.union (fv_term ty) (fv_term te)
    | DestructWith eqs ->
      List.fold_left (fun acc eq -> IndexSet.union acc (fv_equation eq)) IndexSet.empty eqs
    | TyAnnotation (te, ty) -> IndexSet.union (fv_term ty) (fv_term te)
    | SrcInfo (pos, term) -> (fv_term te)

and fv_equation (eq: equation) : IndexSet.t = 
  let (p, _), te = eq in
  IndexSet.union (fv_pattern p) (fv_term te)
and fv_pattern (p: pattern) : IndexSet.t =
  match p with
    | PType | PCste _ -> IndexSet.empty
    | PVar (n, ty) -> fv_term ty
    | PAVar ty -> fv_term ty
    | PAlias (n, p, ty) -> IndexSet.union (fv_term ty) (fv_pattern p)
    | PApp (s, args, ty) ->
      List.fold_left (fun acc (p, _) -> IndexSet.union acc (fv_pattern p)) (fv_term ty) args


(* function like map, but that can skip elements *)
let rec skipmap (f: 'a -> 'b option) (l: 'a list) : 'b list =
  match l with
    | [] -> []
    | hd::tl -> 
      match f hd with
	| None -> skipmap f tl
	| Some hd -> hd::(skipmap f tl)

(* function that map symbol into string *)
let symbol2string (s: symbol) =
  match s with
    | Name n -> n
    | Symbol (n, o) ->
      let (pre, post) = 
	match o with
	  | NoFix -> "", ""
	  | Prefix _ -> "[", ")"
	  | Infix _ -> "(", ")"
	  | Postfix _ -> "(", "]"
      in
      String.concat "" [pre; n; post]

(* get a bound variable frame *)
let get_bvar_frame (ctxt: context) (i: index) : frame =
  try 
    List.nth ctxt i
  with
    | Failure _ -> raise (DoudouException (NoSuchBVar (i, ctxt)))
    | Invalid_argument _ -> raise (DoudouException (NegativeIndexBVar i))

(*
  the priority of operators
  the greater, the more strongly binding
  NoFix have 0
*)
let op_priority (o: op) : int =
  match o with
    | NoFix -> 0
    | Prefix i -> i
    | Infix (i, _) -> i
    | Postfix i -> i

(* returns only the elements that are explicit *)
let filter_explicit (l: ('a * nature) list) : 'a list =
  List.map fst (List.filter (fun (_, n) -> n = Explicit) l)
    

(* this function take a term te1 and
   return a list of pattern ps and a term te2 such that
   List.fold_right (fun p acc -> DestructWith p acc) ps te2 == te1
   
   less formally, traversing a term to find the maximum list of DestructWith with only one equation (the next visited term being the r.h.s of the equation)
*)

let rec accumulate_pattern_destructwith (te: term) : (pattern * nature) list * term =
  match te with
    | DestructWith ([(p, te)]) ->
      let (ps, te) = accumulate_pattern_destructwith te in
      (p::ps, te)
    | _ -> ([], te)

(* returns the numbers of bvars introduced by a pattern 
   we should always have 
   pattern_size p = List.length (fst (pattern_bvars p)))
*)
let rec pattern_size (p: pattern) : int =
  match p with
    | PType -> 0
    | PVar (n, ty) -> 1
    | PAVar ty -> 0
    | PCste s -> 0
    | PAlias (n, p, ty) -> 1 + pattern_size p
    | PApp (s, args, ty) -> 
      List.fold_left ( fun acc (hd, _) -> acc + pattern_size hd) 0 args

(* utilities for DoudouException *)

(* makes error more precise *)
let error_left_pos (err: doudou_error) (pos: pos) =
  match err with
    (* there is no pos information for first element *)
    | ErrorPosPair (None, pos2, err) -> ErrorPosPair (Some pos, pos2, err)
    (* our source information is better *)
    | ErrorPosPair (Some pos1, pos2, err) when pos_in pos1 pos -> ErrorPosPair (Some pos, pos2, err)
    (* the given source information is better *)
    | ErrorPosPair (Some pos1, pos2, err) when pos_in pos pos1 -> ErrorPosPair (Some pos1, pos2, err)
    (* else ... *)
    | err -> ErrorPosPair (Some pos, None, err)

let error_right_pos (err: doudou_error) (pos: pos) =
  match err with
    (* there is no pos information for first element *)
    | ErrorPosPair (pos1, None, err) -> ErrorPosPair (pos1, Some pos, err)
    (* our source information is better *)
    | ErrorPosPair (pos1, Some pos2, err) when pos_in pos2 pos -> ErrorPosPair (pos1, Some pos, err)
    (* the given source information is better *)
    | ErrorPosPair (pos1, Some pos2, err) when pos_in pos pos2 -> ErrorPosPair (pos1, Some pos2, err)
    (* else ... *)
    | err -> ErrorPosPair (Some pos, None, err)

let error_pos (err: doudou_error) (pos: pos) =
  match err with
    (* our source information is better *)
    | ErrorPos (pos1, err) when pos_in pos1 pos -> ErrorPos (pos, err)
    (* the given source information is better *)
    | ErrorPos (pos1, err) when pos_in pos pos1 -> ErrorPos (pos1, err)
    (* else ... *)
    | err -> ErrorPos (pos, err)


(***************************)
(*      substitution       *)
(***************************)


module IndexMap = Map.Make(
  struct
    type t = int
    let compare x y = compare x y
  end
);;

(* substitution: from free variables to term *) 
type substitution = term IndexMap.t;;

(* substitution *)
let rec term_substitution (s: substitution) (te: term) : term =
  match te with
    | Type | Cste _ | Obj _ -> te
    | TVar i as v when i < 0 -> 
      (
	try IndexMap.find i s 
	with
	  | Not_found -> v
      )
    | TVar i as v when i >= 0 -> v
    | AVar -> raise (Failure "term_substitution catastrophic: AVar")
    | TName _ -> raise (Failure "term_substitution catastrophic: TName")
    | App (te, args) ->
      App (term_substitution s te,
	   List.map (fun (te, n) -> term_substitution s te, n) args)
    | Impl ((symb, ty, n), te) ->
      Impl ((symb, term_substitution s ty, n),
	    term_substitution s te)
    | DestructWith eqs ->
      DestructWith (List.map (equation_substitution s) eqs)
    | TyAnnotation (te, ty) -> TyAnnotation (term_substitution s te, term_substitution s ty)
    | SrcInfo (pos, te) -> SrcInfo (pos, term_substitution s te)
and equation_substitution (s: substitution) (eq: equation) : equation =
  let (p, n), te = eq in
  (pattern_substitution s p, n), term_substitution (shift_substitution s (pattern_size p)) te
and pattern_substitution (s: substitution) (p: pattern) : pattern =
  match p with
    | PType -> PType
    | PVar (n, ty) -> PVar (n, term_substitution s ty)
    | PCste s -> PCste s
    | PAlias (n, p, ty) -> PAlias (n, pattern_substitution s p, term_substitution s ty)
    | PApp (symb, args, ty) ->
      PApp (symb,
	    List.map (fun (p, n) -> pattern_substitution s p, n) args,
	    term_substitution s ty)

(* shift bvar index in a substitution *)
and shift_substitution (s: substitution) (delta: int) : substitution =
  IndexMap.fold (fun key value acc -> 
    try 
      IndexMap.add key (shift_term value delta) acc
    with
      | DoudouException (Unshiftable_term _) -> acc
  ) s IndexMap.empty

(* shift bvar index in a term *)
and shift_term (te: term) (delta: int) : term =
  leveled_shift_term te 0 delta

(* shift bvar index in a term, above a given index *)
and leveled_shift_term (te: term) (level: int) (delta: int) : term =
  match te with
    | Type -> Type
    | Cste s -> Cste s
    | Obj o -> Obj o
    | TVar i as v ->
      if i >= level then
	if i + delta < level then
	  raise (DoudouException (Unshiftable_term (te, level, delta)))
	else
	  TVar (i + delta)
      else
	v
    | AVar -> raise (Failure "leveled_shift_term catastrophic: AVar")
    | TName _ -> raise (Failure "leveled_shift_term catastrophic: TName")

    | App (te, args) ->
      App (
	leveled_shift_term te level delta,
	List.map (fun (te, n) -> leveled_shift_term te level delta, n) args
      )
    | Impl ((s, ty, n), te) ->
      Impl ((s, leveled_shift_term ty level delta, n), leveled_shift_term te (level + 1) delta)

    | DestructWith eqs ->
      DestructWith (List.map (fun eq -> leveled_shift_equation eq level delta) eqs)

    | TyAnnotation (te, ty) -> TyAnnotation (leveled_shift_term te level delta, leveled_shift_term ty level delta)

    | SrcInfo (pos, te) -> SrcInfo (pos, leveled_shift_term te level delta)

and leveled_shift_equation (eq: equation) (level: int) (delta: int) : equation =
  let (p, n), te = eq in
  (leveled_shift_pattern p level delta, n), leveled_shift_term te (level + pattern_size p) delta

and leveled_shift_pattern (p: pattern) (level: int) (delta: int) : pattern =
  match p with
    | PType -> PType
    | PVar (n, ty) -> PVar (n, leveled_shift_term ty level delta)
    | PAVar ty -> PAVar (leveled_shift_term ty level delta)
    | PAlias (s, p, ty) -> PAlias (s, leveled_shift_pattern p level delta, leveled_shift_term ty level delta)
    | PApp (s, args, ty) ->
      PApp (s,
	    List.map (fun (p, n) -> leveled_shift_pattern p level delta, n) args,
	    leveled_shift_term ty level delta)

(***************************)
(*      context/frame      *)
(***************************)

(* build a new frame 
   value is optional
*)
let build_new_frame (s: symbol) ?(value: term = TVar 0) (ty: term) : frame =
{ 
  symbol = s;
  ty = ty;
  value = value;

  fvs = [];
  termstack = [];
  naturestack = [];
  equationstack = [];
  patternstack = [];

}

(* push the bvars of a pattern in a context *)
let push_pattern_bvars (ctxt: context) (l: (name * term * term) list) : context =
  List.fold_left (fun ctxt (n, ty, v) ->
    (
      build_new_frame (Name n) ~value:v ty
    ) :: ctxt	     

  ) ctxt l


(* returns the list of bound variables, their value (w.r.t. other bound variable) and their type in a pattern 
   the order is such that 
   it also returns the overall value of the pattern (under the pattern itself)
   hd::tl -> hd is the "oldest" variable, and is next to be framed
*)

let rec pattern_bvars (p: pattern) : (name * term * term) list * term =
  match p with
    | PType -> [], Type
    | PVar (n, ty) -> [n, ty, TVar 0], TVar 0
    | PAVar ty -> ["_", ty, TVar 0], TVar 0
    | PCste s -> [] , Cste s
    | PAlias (n, p, ty) -> 
      let l, te = pattern_bvars p in
      (* the value is shift by one (under the alias-introduced var) *)
      (l, shift_term te 1)
    | PApp (s, args, ty) -> 
      let (delta, l, rev_values) = 
	(* for sake of optimization the value list is in reverse order *)
	List.fold_left (fun (delta, l, rev_values) (p, n) ->
	  (* first we grab the result for p *)
	  let (pl, te) = pattern_bvars p in
	  (* then we need to shift the value term by the current delta level *)
	  let te = shift_term te delta in
	  (* we update the delta value, and returns the concatenation *)
	  (delta + List.length l, l @ pl, (te, n)::rev_values)
	) (0, [], []) args in
      (l, App (Cste s, List.rev rev_values))


(* compute the context under a pattern *)
let push_pattern (ctxt: context) (p: pattern) : context =
  (* we extract the list of bound variable in the pattern *)
  let (bvars, _) = pattern_bvars p in
  (* we build a new context with the pattern bvars frames pushed *)
  push_pattern_bvars ctxt bvars

(* apply a substitution in a context *)
let context_substitution (s: substitution) (ctxt: context) : context =
  fst (mapacc (fun s frame ->
    { frame with
      ty = term_substitution s frame.ty;
      (* not sure on this one ... there should be no fv in value ... *)
      value = term_substitution s frame.value;
      fvs = List.map (fun (ty, value) -> term_substitution s ty, term_substitution s value) frame.fvs;
      termstack = List.map (term_substitution s) frame.termstack;
      equationstack = List.map (equation_substitution s) frame.equationstack;
      patternstack = List.map (pattern_substitution s) frame.patternstack
    }, shift_substitution s 1
  ) s ctxt
  )

(* grab the value of a fvar *)
let bvar_value (ctxt: context) (i: index) : term =
  try (
    let frame = List.nth ctxt i in
    let value = frame.value in
    shift_term value i
  ) with
    | Failure "nth" -> raise (DoudouException (NoSuchBVar (i, ctxt)))
    | Invalid_argument "List.nth" -> raise (DoudouException (NegativeIndexBVar i))

(*************************************************************)
(*      unification/reduction, type{checking/inference}      *)
(*************************************************************)

(*
  reduction of terms
  several strategy are possible:
  for beta reduction: Lazy or Eager
  possibility to have strong beta reduction
  delta: unfold equations (replace cste with their equations)
  iota: try to match equations l.h.s
  deltaiotaweak: if after delta reduction, a iota reduction fails, then the delta reduction is backtracked
  zeta: compute the let bindings
  eta: not sure if needed

  all these different strategy are used for several cases: unification, typechecking, ...
  
*)

type strategy = 
  | Lazy 
  | Eager

type reduction_strategy = {
  strat: strategy;
  beta: bool;
  betastrong: bool;
  delta: bool;
  iota: bool;
  deltaiotaweak: bool;
  zeta: bool;
  eta: bool;
}

let unification_strat : reduction_strategy = {
  strat = Lazy;
  beta = true;
  betastrong = false;
  delta = true;
  iota = true;
  deltaiotaweak = false;
  zeta = true;
  eta = true;
}

(* something's wrong: we do not push terms such that they can be substituted with the generated unifiers !!! *)
let rec unification_term_term (defs: defs) (ctxt: context ref) (te1: term) (te2: term) : term =
  match te1, te2 with

    (* first the cases for SrcInfo and TyAnnotation *)

    | SrcInfo (pos, te1), _ -> (
      try 
	unification_term_term defs ctxt te1 te2
      with
	| DoudouException err -> raise (DoudouException (error_left_pos err pos))
    )

    | _, SrcInfo (pos, te2) -> (
      try 
	unification_term_term defs ctxt te1 te2
      with
	| DoudouException err -> raise (DoudouException (error_right_pos err pos))
    )

    | TyAnnotation (te1, ty1), TyAnnotation (te2, ty2) ->
      let te = unification_term_term defs ctxt te1 te2 in
      let ty = unification_term_term defs ctxt ty1 ty2 in
      TyAnnotation (te, ty)

    (* and the two cases above, we need to unify the annotated type with the infered type 
       not sure this is really needed ... but 
    *)
    | TyAnnotation (te1, ty1), _ ->
      let (te2, ty2) = typeinfer defs ctxt te2 in
      unification_term_term defs ctxt (TyAnnotation (te1, ty1)) (TyAnnotation (te2, ty2))

    | _, TyAnnotation (te2, ty2) ->
      let (te1, ty1) = typeinfer defs ctxt te1 in
      unification_term_term defs ctxt (TyAnnotation (te1, ty1)) (TyAnnotation (te2, ty2))

    (* the error cases for AVar and TName *)
    | AVar, _ -> raise (Failure "unification_term_term catastrophic: AVar in te1 ")
    | _, AVar -> raise (Failure "unification_term_term catastrophic: AVar in te2 ")
    | TName _, _ -> raise (Failure "unification_term_term catastrophic: TName in te1 ")
    | _, TName _ -> raise (Failure "unification_term_term catastrophic: TName in te2 ")


    (* the trivial cases for Type, Cste and Obj *)
    | Type, Type -> Type
    | Obj o1, Obj o2 when o1 = o2 -> Obj o1
    | Cste c1, Cste c2 when c1 = c2 -> Cste c1
    (* when a term is a constant we just look for its definition and expand *)
    | Cste c1, _ -> (
      try 
	unification_term_term defs ctxt (snd (Hashtbl.find defs.store (symbol2string c1))) te2
      with
	| Not_found -> raise (DoudouException (UnknownCste c1))
    )
    | _, Cste c2 -> (
      try 
	unification_term_term defs ctxt te1 (snd (Hashtbl.find defs.store (symbol2string c2)))
      with
	| Not_found -> raise (DoudouException (UnknownCste c2))
    )

    (* the trivial case for variable *)
    | TVar i1, TVar i2 when i1 = i2 -> TVar i1
    (* the case for free variables *)
    (* we need the free var to not be a free var of the term *)
    | TVar i1, _ when i1 < 0 && not (IndexSet.mem i1 (fv_term te2))->
      let s = IndexMap.singleton i1 te2 in
      ctxt := context_substitution s (!ctxt);
      (* should we rewrite subst in te2 ? a priori no:
	 1- i not in te2
	 2- if s introduce a possible substitution, it means that i was in te2 by transitives substitution
	 and that we did not comply with the N.B. above
      *)
      te2      
	  
    | _, TVar i2 when i2 < 0 && not (IndexSet.mem i2 (fv_term te1))->
      let s = IndexMap.singleton i2 te1 in
      ctxt := context_substitution s (!ctxt);
      (* should we rewrite subst in te2 ? a priori no:
	 1- i not in te2
	 2- if s introduce a possible substitution, it means that i was in te2 by transitives substitution
	 and that we did not comply with the N.B. above
      *)
      te1
    (* in other cases, the frame contains the value for a given bound variable. If its not itself, we should unfold *)
    | TVar i1, _ when i1 >= 0 && bvar_value !ctxt i1 != TVar i1 ->
      unification_term_term defs ctxt (bvar_value !ctxt i1) te2
    | _, TVar i2 when i2 >= 0 && bvar_value !ctxt i2 != TVar i2 ->
      unification_term_term defs ctxt te1 (bvar_value !ctxt i2)

    (* the case of two application: with not the same arity *)
    | App (hd1, args1), App (hd2, args2) when List.length args1 != List.length args2 ->
      (* first we try to change them such that they have the same number of arguments and try to match them *)
      let min_arity = min (List.length args1) (List.length args2) in
      let te1' = if List.length args1 = min_arity then te1 else App (App (hd1, take (List.length args1 - min_arity) args1), drop (List.length args1 - min_arity) args1) in
      let te2' = if List.length args2 = min_arity then te2 else App (App (hd2, take (List.length args2 - min_arity) args2), drop (List.length args2 - min_arity) args2) in
      (* we save the current context somewhere to rollback *)
      let saved_ctxt = !ctxt in
      (try 
	 unification_term_term defs ctxt te1' te2' 
       with
	 (* apparently it does not work, so we try to reduce them *)
	 | DoudouException _ ->
	   (* restore the context *)
	   ctxt := saved_ctxt;
	   (* reducing them *)
	   let te1' = reduction defs ctxt unification_strat te1 in
	   let te2' = reduction defs ctxt unification_strat te2 in
	   (* if both are still the sames, we definitely do not know if they can be unify, else we try to unify the new terms *)
	   if te1 = te1' && te2 = te2' then raise (DoudouException (UnknownUnification (!ctxt, te1, te2))) else unification_term_term defs ctxt te1' te2'
      )
    (* the case of two application with same arity *)
    | App (hd1, args1), App (hd2, args2) when List.length args1 = List.length args2 ->
      (* first we save the context and try to unify all term component *)
      let saved_ctxt = !ctxt in
      (try
	 (**)
	 (* first we unify the head of applications *)
	 let hd = unification_term_term defs ctxt hd1 hd2 in
	 (* then we unify all the arguments pair-wise *)
	 let args = List.map (fun ((te1, n1), (te2, n2)) ->
	   if n1 != n2 then
	     (* if both nature are different -> no unification ! *)
	     raise (DoudouException (NoUnification (!ctxt, te1, te2)))
	   else
	     let te = unification_term_term defs ctxt te1 te2 in
	     (te, n1)
	 ) (List.combine args1 args2) in
	 (* finally we have our unified term ! *)
	 App (hd, args)

       with
	 (* apparently it does not work, so we try to reduce them *)
	 | DoudouException _ ->
	   (* restore the context *)
	   ctxt := saved_ctxt;
	   (* reducing them *)
	   let te1' = reduction defs ctxt unification_strat te1 in
	   let te2' = reduction defs ctxt unification_strat te2 in
	   (* if both are still the sames, we definitely do not know if they can be unify, else we try to unify the new terms *)
	   if te1 = te1' && te2 = te2' then raise (DoudouException (UnknownUnification (!ctxt, te1, te2))) else unification_term_term defs ctxt te1' te2'
      )	
    (* the cases where only one term is an Application: we should try to reduce it if possible, else we do not know! *)
    | App (hd1, args1), _ ->
      let te1' = reduction defs ctxt unification_strat te1 in
      if te1 = te1' then raise (DoudouException (UnknownUnification (!ctxt, te1, te2))) else unification_term_term defs ctxt te1' te2
    | _, App (hd2, args2) ->
      let te2' = reduction defs ctxt unification_strat te2 in
      if te2 = te2' then raise (DoudouException (UnknownUnification (!ctxt, te1, te2))) else unification_term_term defs ctxt te1 te2'

    (* the impl case: only works if both are impl *)
    | Impl ((s1, ty1, n1), te1), Impl ((s2, ty2, n2), te2) ->
      (* the symbol is not important, yet the nature is ! *)
      if n1 != n2 then raise (DoudouException (NoUnification (!ctxt, te1, te2))) else
	(* we unify the types *)
	let ty = unification_term_term defs ctxt ty1 ty2 in
	(* we push a frame *)
	let frame = build_new_frame s1 ty in
	ctxt := frame::!ctxt;
	(* we unify *)
	let te = unification_term_term defs ctxt te1 te2 in
	(* we pop the frame *)
	ctxt := List.tl !ctxt;
	(* and we return the term *)
	Impl ((s1, ty, n1), te)

    (* for now we do not allow unification of DestructWith *)
    | DestructWith eqs1, DestructWith eq2 ->
      printf "unification_term_term: DestructWith\n";
      raise (DoudouException (UnknownUnification (!ctxt, te1, te2)))

    (* for all the rest: I do not know ! *)
    | _ -> 
      printf "unification_term_term: case not explicitely defined\n";
      raise (DoudouException (UnknownUnification (!ctxt, te1, te2)))

and reduction (defs: defs) (ctxt: context ref) (strat: reduction_strategy) (te: term) : term = 
  raise (Failure "reduction: NYI")

and typecheck (defs: defs) (ctxt: context ref) (te: term) (ty: term) : term * term =
  raise (Failure "NYI")
and typeinfer (defs: defs) (ctxt: context ref) (te: term) : term * term =
  raise (Failure "NYI")

      
(******************)
(* pretty printer *)
(******************)

(*
  helper functions
*)
let rec intercalate (inter: 'a) (l: 'a list) : 'a list =
  match l with
    | hd1::hd2::tl ->
      hd1::inter::(intercalate inter (hd2::tl))
    | _ -> l

let rec intercalates (inter: 'a list) (l: 'a list) : 'a list =
  match l with
    | hd1::hd2::tl ->
      hd1::inter @ intercalates inter (hd2::tl)
    | _ -> l

let rec withParen (t: token) : token =
  Box [Verbatim "("; t; Verbatim ")"]

let rec withBracket (t: token) : token =
  Box [Verbatim "{"; t; Verbatim "}"]

(* a data structure to mark the place where the term/pattern is *)
type place = InNotation of op * int (* in the sndth place of the application to the notation with op *)
	     | InApp (* in the head of application *)
	     | InArg of nature (* as an argument (Explicit) *)
	     | InAlias  (* in an alias pattern *)
	     | Alone (* standalone *)

(* TODO: add options for 
   - printing implicit terms 
   - printing type annotation
   - source info
*)

(* transform a term into a box *)
let rec term2token (ctxt: context) (te: term) (p: place): token =
  match te with
    | Type -> Verbatim "Type"
    | Cste s -> Verbatim (symbol2string s)
    | Obj o -> o#pprint ()
    | TVar i when i >= 0 -> 
      let frame = get_bvar_frame ctxt i in
      Verbatim (symbol2string (frame.symbol))
    | TVar i when i < 0 -> 
      Verbatim (String.concat "" ["["; string_of_int i;"]"])

    (* we need to split App depending on the head *)
    (* the case for notation Infix *)
    | App (Cste (Symbol (s, Infix (myprio, myassoc))), args) when List.length (filter_explicit args) = 2->
      (* we should put parenthesis in the following condition: *)
      (match p with
	(* if we are an argument *)
	| InArg Explicit -> withParen
	(* if we are in a notation such that *)
	(* a prefix or postfix binding more  than us *)
	| InNotation (Prefix i, _) when i > myprio -> withParen
	| InNotation (Postfix i, _) when i > myprio -> withParen
	(* or another infix with higher priority *)
	| InNotation (Infix (i, _), _) when i > myprio -> withParen
	(* or another infix with same priority depending on the associativity and position *)
	(* I am the first argument and its left associative *)
	| InNotation (Infix (i, LeftAssoc), 1) when i = myprio -> withParen
	(* I am the second argument and its right associative *)
	| InNotation (Infix (i, RightAssoc), 2) when i = myprio -> withParen

	(* else we do not need parenthesis *)
	| _ -> fun x -> x
      )	(
	match filter_explicit args with
	  | arg1::arg2::[] ->
	    let arg1 = term2token ctxt arg1 (InNotation (Infix (myprio, myassoc), 1)) in
	    let arg2 = term2token ctxt arg2 (InNotation (Infix (myprio, myassoc), 2)) in
	    let te = Verbatim s in
	    Box (intercalate (Space 1) [arg1; te; arg2])
	  | _ -> raise (Failure "term2token, App infix case: irrefutable patten")
       )
    (* the case for Prefix *)
    | App (Cste (Symbol (s, (Prefix myprio))), args) when List.length (filter_explicit args) = 1 ->
      (* we put parenthesis when
	 - as the head or argument of an application
	 - in a postfix notation more binding than us
      *)
      (match p with
	| InArg Explicit -> withParen
	| InApp -> withParen
	| InNotation (Postfix i, _) when i > myprio -> withParen
	| _ -> fun x -> x
      ) (
	match filter_explicit args with
	  | arg::[] ->
	    let arg = term2token ctxt arg (InNotation (Prefix myprio, 1)) in
	    let te = Verbatim s in
	    Box (intercalate (Space 1) [te; arg])
	  | _ -> raise (Failure "term2token, App prefix case: irrefutable patten")
       )

    (* the case for Postfix *)
    | App (Cste (Symbol (s, (Postfix myprio))), args) when List.length (filter_explicit args) = 1 ->
      (* we put parenthesis when
	 - as the head or argument of an application
	 - in a prefix notation more binding than us
      *)
      (match p with
	| InArg Explicit -> withParen
	| InApp -> withParen
	| InNotation (Prefix i, _) when i > myprio -> withParen
	| _ -> fun x -> x
      ) (
	match filter_explicit args with
	  | arg::[] ->
	    let arg = term2token ctxt arg (InNotation (Postfix myprio, 1)) in
	    let te = Verbatim s in
	    Box (intercalate (Space 1) [arg; te])
	  | _ -> raise (Failure "term2token, App postfix case: irrefutable patten")
       )

    (* general case *)
    | App (te, args) ->
      (* we only embed in parenthesis if
	 - we are an argument of an application
	 - we are in a notation
      *)
      (match p with
	| InArg Explicit -> withParen
	| InNotation _ -> withParen
	| _ -> fun x -> x
      ) (
	let args = List.map (fun te -> term2token ctxt te (InArg Explicit)) (filter_explicit args) in
	let te = term2token ctxt te InApp in
	Box (intercalate (Space 1) (te::args))
       )

    (* implication *)
    | Impl ((s, ty, nature), te) ->
      (* we embed in parenthesis if 
	 - embed as some arg 
	 - ??
      *)
      (
	match p with
	  | InArg Explicit -> withParen
	  | _ -> fun x -> x
      )
	(
	  (* the lhs of the ->*)
	  let lhs = 
	    (* if the symbol is NoFix _ -> we skip the symbol *)
	    (* IMPORTANT: it means that Symbol ("_", NoFix)  as a special meaning !!!! *)
	    match s with
	      | Symbol ("_", NoFix) ->
		(* we only put brackets if implicit *)
		(if nature = Implicit then withBracket else fun x -> x)
		  (term2token ctxt ty (InArg nature))
	      | _ -> 
		(* here we put the nature marker *)
		(if nature = Implicit then withBracket else withParen)
		  (Box [Verbatim (symbol2string s); Space 1; Verbatim "::"; Space 1; term2token ctxt ty Alone])
	  in 
	  (* for computing the r.h.s, we need to push a new frame *)
	  let newframe = build_new_frame s ty in
	  let rhs = term2token (newframe::ctxt) te Alone in
	  Box [lhs; Space 1; Verbatim "->"; Space 1; rhs]
	)

    | DestructWith eqs ->
      (* we do not put parenthesis only when
	 - we are alone
      *)
      (
	match p with
	  | Alone -> (fun x -> x)
	  | _ -> withParen
      )
      (
	(* we extract the accumulation of destructwith *)
	let (ps, te) = accumulate_pattern_destructwith te in
	match ps with
	  (* if ps is empty -> do something basic *)
	  | [] ->
	    let eqs = List.map (fun eq -> equation2token ctxt eq) eqs in
	    Box (intercalates [Newline; Verbatim "|"; Space 1] eqs)
	  (* else we do more prettty printing *)
	  | _ ->
	    let (ps, ctxt) = List.fold_left (fun (ps, ctxt) (p, nature)  -> 

	      (* N.B.: we are printing even the implicit arguments ... is it always a good thing ? *)

	      (* we print the pattern *)
	      let pattern = (if nature = Implicit then withBracket else fun x -> x) (pattern2token ctxt p (InArg nature)) in
	      (* grab the underlying context *)
	      let ctxt = push_pattern ctxt p in
	      (* we return the whole thing *)
	      (* NB: for sake of optimization we return a reversed list of pattern, which are reversed in the final box *)
	      ((pattern::ps), ctxt)
	    ) ([], ctxt) ps in
	      let te = term2token ctxt te Alone in
	      Box (intercalate (Space 1) (List.rev ps) @ [Space 1; Verbatim ":="; Space 1; te])
      )
    | TyAnnotation (te, _) | SrcInfo (_, te) ->
      term2token ctxt te p      

    | AVar -> raise (Failure "term2token - catastrophic: still an AVar in the term")
    | TName _ -> raise (Failure "term2token - catastrophic: still an TName in the term")


and equation2token (ctxt: context) (eq: equation) : token =
  (* here we simply print the DestructWith with only one equation *)
  term2token ctxt (DestructWith [eq]) Alone

and pattern2token (ctxt: context) (pattern: pattern) (p: place) : token =
  match pattern with
    | PType -> Verbatim "Type"
    | PVar (n, _) -> Verbatim n
    | PAVar _ -> Verbatim "_"
    | PCste s -> Verbatim (symbol2string s)
    | PAlias (n, pattern, _) -> Box [Verbatim n; Verbatim "@"; pattern2token ctxt pattern InAlias]

    (* for the append we have several implementation that mimics the ones for terms *)
    | PApp (Symbol (s, Infix (myprio, myassoc)), args, _) when List.length (filter_explicit args) = 2->
      (* we should put parenthesis in the following condition: *)
      (match p with
	(* if we are an argument *)
	| InArg Explicit -> withParen
	(* if we are in a notation such that *)
	(* a prefix or postfix binding more  than us *)
	| InNotation (Prefix i, _) when i > myprio -> withParen
	| InNotation (Postfix i, _) when i > myprio -> withParen
	(* or another infix with higher priority *)
	| InNotation (Infix (i, _), _) when i > myprio -> withParen
	(* or another infix with same priority depending on the associativity and position *)
	(* I am the first argument and its left associative *)
	| InNotation (Infix (i, LeftAssoc), 1) when i = myprio -> withParen
	(* I am the second argument and its right associative *)
	| InNotation (Infix (i, RightAssoc), 2) when i = myprio -> withParen
	(* if we are in an alias *)
	| InAlias -> withParen

	(* else we do not need parenthesis *)
	| _ -> fun x -> x
      ) (
	match filter_explicit args with
	  | arg1::arg2::[] ->
	    let arg1 = pattern2token ctxt arg1 (InNotation (Infix (myprio, myassoc), 1)) in
	    let arg2 = pattern2token ctxt arg2 (InNotation (Infix (myprio, myassoc), 2)) in
	    let te = Verbatim s in
	    Box (intercalate (Space 1) [arg1; te; arg2])
	  | _ -> raise (Failure "pattern2token, App infix case: irrefutable patten")
       )
    (* the case for Prefix *)
    | PApp (Symbol (s, (Prefix myprio)), args, _) when List.length (filter_explicit args) = 1 ->
      (* we put parenthesis when
	 - as the head or argument of an application
	 - in a postfix notation more binding than us
	 - in an alias
      *)
      (match p with
	| InArg Explicit -> withParen
	| InApp -> withParen
	| InAlias -> withParen
	| InNotation (Postfix i, _) when i > myprio -> withParen
	| _ -> fun x -> x
      ) (
	match filter_explicit args with
	  | arg::[] ->
	    let arg = pattern2token ctxt arg (InNotation (Prefix myprio, 1)) in
	    let te = Verbatim s in
	    Box (intercalate (Space 1) [te; arg])
	  | _ -> raise (Failure "pattern2token, App prefix case: irrefutable patten")
       )

    (* the case for Postfix *)
    | PApp (Symbol (s, (Postfix myprio)), args, _) when List.length (filter_explicit args) = 1 ->
      (* we put parenthesis when
	 - as the head or argument of an application
	 - in a prefix notation more binding than us
	 - in an alias
      *)
      (match p with
	| InArg Explicit -> withParen
	| InApp -> withParen
	| InNotation (Prefix i, _) when i > myprio -> withParen
	| InAlias -> withParen
	| _ -> fun x -> x
      ) (
	match filter_explicit args with
	  | arg::[] ->
	    let arg = pattern2token ctxt arg (InNotation (Postfix myprio, 1)) in
	    let te = Verbatim s in
	    Box (intercalate (Space 1) [arg; te])
	  | _ -> raise (Failure "term2token, App postfix case: irrefutable patten")
       )

    (* general case *)
    | PApp (s, args, _) ->
      (* we only embed in parenthesis if
	 - we are an argument of an application
	 - we are in a notation
      *)
      (match p with
	| InArg Explicit -> withParen
	| InNotation _ -> withParen
	| InAlias -> withParen
	| _ -> fun x -> x
      ) (
	let args = List.map (fun te -> pattern2token ctxt te (InArg Explicit)) (filter_explicit args) in
	let s = symbol2string s in
	Box (intercalate (Space 1) (Verbatim s::args))
       )


(* make a string from a term *)
let term2string (ctxt: context) (te: term) : string =
  let token = term2token ctxt te Alone in
  let box = token2box token 80 2 in
  box2string box

(**********************************)
(* parser (lib/parser.ml version) *)
(**********************************)

let with_start_pos (startp: (int * int)) (p: 'a parsingrule) : 'a parsingrule =
  fun pb ->
    let curp = cur_pos pb in
    if (snd startp <= snd curp) then raise NoMatch;
    p pb

let doudou_keywords = []

open Str;;

let name_parser : name parsingrule = applylexingrule (regexp "[a-zA-Z][a-zA-Z0-9]*", 
						      fun (s:string) -> 
							if List.mem s doudou_keywords then raise NoMatch else s
)

let parse_avar : unit parsingrule = applylexingrule (regexp "_", 
						     fun (s:string) -> ()
)
  
(******************************)
(*        tests               *)
(******************************)

(* pretty printer *)

let zero = Cste (Name "0")
let splus = (Symbol ("+", Infix (30, LeftAssoc)))
let plus = Cste splus
let minus = Cste (Symbol ("-", Infix (30, LeftAssoc)))
let mult = Cste (Symbol ("*", Infix (40, LeftAssoc)))
let div = Cste (Symbol ("/", Infix (40, LeftAssoc)))
let colon = Cste (Symbol (";", Infix (20, RightAssoc)))
let andc = Cste (Symbol ("&", Postfix 20))
let neg = Cste (Symbol ("-", Prefix 50))

let nat = (Cste (Name "nat"))

let asymb = Symbol ("_", NoFix)

let avar = Cste asymb

let _ = printf "%s\n" (term2string empty_context zero)
let _ = printf "%s\n" (term2string empty_context plus)
let _ = printf "%s\n" (term2string empty_context andc)
let _ = printf "%s\n" (term2string empty_context neg)
let _ = printf "%s\n" (term2string empty_context (App (andc, [App (mult, [zero, Explicit; zero, Explicit]), Explicit])))
let _ = printf "%s\n" (term2string empty_context (App (neg, [App (mult, [zero, Explicit; zero, Explicit]), Explicit])))

let _ = printf "%s\n" (term2string empty_context (
  Impl ((asymb, Impl ((asymb, nat, Explicit), Impl ((asymb, nat, Implicit), nat)), Implicit), Impl ((Name "prout", nat, Explicit), nat))
)
)

let _ = printf "%s\n" (term2string empty_context (
  DestructWith [((PVar ("x", avar), Explicit), DestructWith [((PVar ("y", avar), Implicit), App (plus, [TVar 0, Explicit; TVar 1, Explicit]))])]
)
)

let _ = printf "%s\n" (term2string empty_context (
  DestructWith [
    (
      (PApp (splus, [PVar ("x", avar), Explicit; PVar ("z", avar), Explicit], Cste asymb), Explicit), 
      DestructWith [
	((PVar ("y", avar), Implicit), 
	 App (plus, [TVar 0, Explicit; TVar 1, Explicit])
	)
      ]
    )
  ]
)
)
