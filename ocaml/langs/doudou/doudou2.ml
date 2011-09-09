(* sketch of reimplementation for Doudou *)

(* for parsing *)
open Parser
(* for pretty printing *)
open Pprinter

open Printf


(*********************************)
(* Definitions of data structure *)
(*********************************)

type name = string

module NameMap = Map.Make(
  struct
    type t = string
    let compare x y = compare x y
  end
);;

module NameSet = Set.Make(
  struct
    type t = string
    let compare x y = compare x y
  end
);;

type op = Nofix
	  | Prefix of int
	  | Infix of int * associativity
	  | Postfix of int

type symbol = | Name of name
	      | Symbol of name * op

type index = int

module IndexSet = Set.Make(
  struct
    type t = int
    let compare x y = compare x y
  end
);;

module IndexMap = Map.Make(
  struct
    type t = int
    let compare x y = compare x y
  end
);;

type nature = Explicit
	      | Implicit
	      | Guessed

class virtual ['a, 'b, 'c] tObj =
object 
  method uuid: int = 0
  method virtual get_name: string
  method virtual get_type: 'a
  method virtual pprint: unit -> token
  method virtual apply: 'c -> 'b -> ('a * nature) list -> 'a
end

type universe = Zero
		| Level of int
		| Succ of universe
		| Max of universe list

type term_info = {
  pos: pos;
  ty: term option; (* term ref option ???*)
}

and term = Type of universe * term_info
	   | Cste of symbol * term_info
	   | Obj of (term, context, defs) tObj * term_info
	
	    (* >= 0 -> bounded variable, < 0 -> free variable *)
	    | TVar of index * term_info
		
	    (* these constructors are only valide after parsing, and removed by typechecking *)
	    | AVar of pos * term_info
	    | TName of symbol * term_info

	    (* *)

	    | App of term * (term * nature) list * term_info
	    | Destruct of term * equation list * term_info

	    | Impl of (name * term * nature * pos) * term * term_info
	    | Lambda of (name * term * nature * pos) * term * term_info

	    (* *)
	    | With of term * defs * term_info

(* N.B.: all types are properly scoped w.r.t. bounded var introduce by "preceding" pattern *)
and pattern = PType of universe * term_info 
	      | PVar of name * term_info
	      | PAVar of term_info
	      | PCste of symbol * term_info
	      | PAlias of name * pattern * term_info
	      | PApp of (symbol * term_info) * (pattern * nature) list * term_info

and equation = pattern * term

(* context of a term *)
(* N.B.: all terms are of the level in which they appear *)
and frame = {
  (* the symbol of the frame *)
  name : name;
  (* its type *)
  ty: term;
  (* the nature of the quantification *)
  nature: nature;
  (* its value: most stupid one: itself *)
  value: term;
  (* its position *)
  pos: pos;
    
  (* the free variables 
     - the index (redundant information put for sake of optimization)
     - the type of the free variable
     - its corresponding value (by unification)
  *)
  fvs: (index * term * term) list;

  (* definitions *)
  defs: defs

  (* the stacks *)
  termstack: term list;
  naturestack: nature list;
  patternstack: pattern list;
  
}

(* context *)
and context = frame list

and value = Inductive of symbol list
	    | Axiom
	    | Constructor
	    | Equation of equation list

(* definitions *)
and defs = (symbol * term * value) NameMap.t

(* oracles *)
type oracle = (ctxt * term) -> term option

type doudou_error = NegativeIndexBVar of index
		    | Unshiftable_term of term * int * int

		    | UnknownCste of symbol
		    | UnknownBVar of index * context
		    | UnknownFVar of index * context

		    | UnknownUnification of context * term * term
		    | NoUnification of context * term * term

		    | NoMatchingPattern of context * pattern * term

		    | PoppingNonEmptyFrame of frame

		    | CannotInfer of context * term * doudou_error
		    | CannotTypeCheck of context * term * term * term * doudou_error

		    | FreeError of string

exception DoudouException of doudou_error
