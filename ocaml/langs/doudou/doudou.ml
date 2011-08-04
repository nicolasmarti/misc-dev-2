(* for parsing *)
open Parser
(* for pretty printing *)
open Pprinter

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

	    | TVar of index
		
	    (* this constructor is only valide after parsing, and removed by typechecking *)
	    | AVar

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
  store : (string, (term * equation list)) Hashtbl.t;
  mutable hist : symbol list;
}

type doudou_error = NoSuchBVar of index * context
		    | NegativeIndexBVar of index
		    | Unshiftable_term of term * int * int

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
	  | NoFix -> "[", "]"
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
  raise (Failure "NYI: term_substitution")

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

(******************************)
(* online typechecking parser *)
(******************************)

let with_start_pos (startp: (int * int)) (p: 'a parsingrule) : 'a parsingrule =
  fun pb ->
    let curp = cur_pos pb in
    if (snd startp <= snd curp) then raise NoMatch;
    p pb


(******************************)
(*        tests               *)
(******************************)

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

open Printf

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
