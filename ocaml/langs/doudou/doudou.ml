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

type symbol = Name of name
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
  (* its nature *)
  nature: nature;
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
let filter_explicit (l: (term * nature) list) : term list =
  List.map fst (List.filter (fun (_, n) -> n = Explicit) l)
    
(***************************)
(*      context/frame      *)
(***************************)

let build_new_frame (s: symbol) (ty: term) ?(value: term = TVar 0) (nature: nature) : frame =
{ 
  symbol = s;
  ty = ty;
  nature = nature;
  value = value;

  fvs = [];
  termstack = [];
  naturestack = [];
  equationstack = [];
  patternstack = [];

}

      
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
	  let newframe = build_new_frame s ty nature in
	  let rhs = term2token (newframe::ctxt) te Alone in
	  Box [lhs; Space 1; Verbatim "->"; Space 1; rhs]
	)

    | DestructWith eqs ->
      (* we always put parenthesis here *)
      (
	withParen
      )
      (
	let eqs = List.map (fun eq -> equation2token ctxt eq) eqs in
	Box (intercalates [Newline; Verbatim "|"; Space 1] eqs)
      )
    | TyAnnotation (te, _) | SrcInfo (_, te) ->
      term2token ctxt te p      

    (* by default we do not support *)
    | _ -> raise (Failure "term2token: NYI")

and equation2token (ctxt: context) (eq: equation) : token =
  raise (Failure "equation2token: NYI")

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
let plus = Cste (Symbol ("+", Infix (30, LeftAssoc)))
let minus = Cste (Symbol ("-", Infix (30, LeftAssoc)))
let mult = Cste (Symbol ("*", Infix (40, LeftAssoc)))
let div = Cste (Symbol ("/", Infix (40, LeftAssoc)))
let colon = Cste (Symbol (";", Infix (20, RightAssoc)))
let andc = Cste (Symbol ("&", Postfix 20))
let neg = Cste (Symbol ("-", Prefix 50))

let nat = (Cste (Name "nat"))

let asymb = Symbol ("_", NoFix)

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
