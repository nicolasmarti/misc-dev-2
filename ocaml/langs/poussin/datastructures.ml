(* for parsing *)
open Parser
(* for pretty printing *)
open Pprinter

(* for outputing *)
open Printf


(*********************************)
(* Definitions of data structure *)
(*********************************)

(* name *)
type name = string

(* operator porperties *)
type op = Nofix
	  | Prefix of int
	  | Infix of int * associativity
	  | Postfix of int

(* symbols are names with properties *)
type symbol = name * op

(* indexes, used for 
   - bounded variables (>=0): refers to a frame index 
   - free variables (<0): refers to free variables that must be found by traversing the frames (keeping track of the level of a free variable)
*)
type index = int

(* quantification, used for 
   - forall (->)
   - and their counterpart in arguments of an application

   Explicit arguments are explicitely given
   Implicit arguments might be omited (if explicitely given, surrounded by { ... }): when omitted they can only be guessed through type checking
*)
type nature = Explicit
	      | Implicit




(* object here are used to implement primitives that cannot be build by the core language *)
class virtual ['a] tObj =
object 
  method uuid: int = 0
  method virtual get_name: string
  method virtual get_type: 'a
  method virtual pprint: unit -> token
  method virtual apply: ('a * nature) list -> 'a
end

(* the universe stratifications  *)
type universe =
  | Zero
  | Level of name
  | Succ of universe
  | Max of universe list
;;

(* terms (representing computations, types and kinds) *)
type term = 

    (* stratified types *)
    Type of universe	
	
  (* constantes refers to definitions in the contexts (to the innermost level in case of redefinitions) *)
  | Cste of symbol

  (* contructions for primitives *)
  | Obj of term tObj

  (* a bounded (index >= 0) or free variables (< 0) which informations are stored in the context *)
  | TVar of index * term

  (* a pattern variable, it has only a semantics (by reduction) in the l.h.s of a destruction 
     in the type semantics, it adds a new frame (= bounded variable)
  *)
  | PVar of name * term

  (* an alias: correspond to an alias for a term. at the typecehcking level it adds a new frame (a bounded variable) *)
  | PAlias of name * term

  (******************************************************)
  (* these constructors are only valide after parsing, and removed by typechecking *)
  (* an anonymous term _, which will be replaced by a free variable at typechecking time *)
  | AVar
  (* a symbol, which will be replaced by the corresponding innermost bounded variable or definition (looked in this order for each frame)*)
  | TSymbol of symbol
  (******************************************************)

  (* application 
     head, arguments, type
  *)
  | App of term * (term * nature) list * term

  (* implication, the dependant product *)
  | Impl of (name * term * nature) * term

  (* the quantification for computations
     this is the compression of \, let, and caseof/matchwith
  *)
  | DestructWith of equation list * term

  (* source information given by the parser in order to reports errors *)
  | SrcInfo of pos * term

(* N.B.: the types annotation are valids for the terms under there 
   bounded variables introduced by PVar/PAlias
*)

(* a pattern is a term and a nature (counterpart of the nature in an implication) *)
and equation = (term * nature) * term

type definition = Inductive of (symbol, term) (* an inductive type with its terms *)
		  | Constructor (* a constructor *)
		  | NoDef (* a symbol without definitions *)

(* context of a term *)
(* N.B.: all terms are of the level in which they appear *)
type frame = {
  (* the name of the bounded variable of the frame *)
  name : name;
  (* its type *)
  ty: term;
  (* the nature of the quantification *)
  nature: nature;
  (* its value: most stupid one: itself == TVar 0*)
  value: term;
    
  (* the free variables 
     - the index (redundant information put for sake of optimization)
     - the type of the free variable
     - its corresponding value (by unification)
  *)
  fvs: (index * term * term) list;

  (* the stacks used to push terms to there corresponding level, in order for them to be substituted with the result of depper unification *)
  termstack: term list;
  naturestack: nature list;
  equationstack: equation list;

  (* a store of definition (lookuped through the Cste term) *)
  store : (string, (symbol * term * definition)) Hashtbl.t; 
}

let empty_frame = {
  name = "";
  ty = AVar;
  nature = Explicit;
  value = AVar;

  fvs = [];

  termstack = [];
  naturestack = [];
  equationstack = [];

  store = Hashtbl.create 10;
}

type context = frame list

(* the context must a least have one frame, for the toplevel *)
let empty_context = empty_frame::[]
	   
(* definition of the possible errors 
   and the corresponding exception
*)
type poussin_error = FreeError of string

exception PoussinException of poussin_error

module IndexMap = Map.Make(
  struct
    type t = int
    let compare x y = compare x y
  end
);;

module IndexSet = Set.Make(
  struct
    type t = int
    let compare x y = compare x y
  end
);;

(* substitution: from free variables to term *) 
type substitution = term IndexMap.t;;

(*
  reduction of terms
  several strategy are possible:
  for beta reduction: Lazy or Eager
  possibility to have strong beta reduction
  delta: unfold equations (replace cste with their equations)
  iota: try to match equations l.h.s
  deltaiotaweak: if after delta reduction (on head of app), a iota reduction fails, then the delta reduction is backtracked
  deltaiotaweak_armed: just a flag to tell the reduction function that it should raise a IotaReductionFailed
  zeta: compute the let bindings
  eta: not sure if needed

  all these different strategy are used for several cases: unification, typechecking, ...
  
*)
type strategy = 
  | Lazy 
  | Eager

type reduction_strategy = {
  beta: strategy;
  betastrong: bool;
  delta: bool;
  iota: bool;
  deltaiotaweak: bool;
  deltaiotaweak_armed: bool;
  zeta: bool;
  eta: bool;
}

(* a special exception for the reduction which 
   signals that an underlying iota reduction fails
*)
exception IotaReductionFailed
