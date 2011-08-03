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

and equation = (pattern * nature) list * term

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

let rec withParen (t: token) : token =
  Box [Verbatim "("; t; Verbatim ")"]

let rec withBracket (t: token) : token =
  Box [Verbatim "{"; t; Verbatim "}"]

(* a data structure to mark the place where the term/pattern is *)
type place = InNotation of op * int (* in the sndth place of the application to the notation with op *)
	     | InApp (* in the head of application *)
	     | InArg (* as an argument (Explicit) *)
	     | InAlias  (* in an alias pattern *)
	     | Alone (* standalone *)

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
	| InArg -> withParen
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
	    Box (intercalate (Space 1) (te::arg1::arg2::[]))
	  | _ -> raise (Failure "term2token, App infix case: irrefutable patten")
       )
    (* general case *)
    | App (te, args) ->
      (* we only embed in parenthesis if
	 - we are an argument of an application
	 - we are in a notation
      *)
      (match p with
	| InArg -> withParen
	| InNotation _ -> withParen
	| _ -> fun x -> x
      ) (
	let args = List.map (fun te -> term2token ctxt te InArg) (filter_explicit args) in
	let te = term2token ctxt te InApp in
	Box (intercalate (Space 1) (te::args))
       )
    | _ -> raise (Failure "term2token: NYI")


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


