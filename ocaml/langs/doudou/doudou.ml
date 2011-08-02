(* for parsing *)
open Parser;;
(* for pretty printing *)
open Pprinter;;

(*********************************)
(* Definitions of data structure *)
(*********************************)

type name = string

type op = NoFix
	  | Prefix of int
	  | Infix of int * associativity
	  | PostFix of int

type symbol = Name of name
	      | Symbol of name * op

type ('a, 'b) either = Left of 'a
		       | Right of 'b

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
end;;

type term = Type
	    | Cste of symbol
	    | Obj of term tObj

	    | TVar of index
	    | AVar

	    | App of term * (term * nature) list
	    | Impl of (symbol * term * nature) * term
	    | CaseOf of equation list

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
    
  (* the free variables *)
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
  store : (string, (term * equation list)) Hashtbl.t;
  mutable hist : symbol list;
}

type doudou_error 

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
";;

(******************)
(* pretty printer *)
(******************)


(******************************)
(* online typechecking parser *)
(******************************)

let with_start_pos (startp: (int * int)) (p: 'a parsingrule) : 'a parsingrule =
  fun pb ->
    let curp = cur_pos pb in
    if (snd startp <= snd curp) then raise NoMatch;
    p pb
;;

