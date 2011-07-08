open Planck;;
module Pos = Position.File
;;

open Op_prec;;

(*
  >= 0 -> quantified var with debruijn index
  < 0 -> free var
*)
type index = int

type name = string

type symbol = Name of name
	      | Symbol of name * op

module SymbolMap = Map.Make(
  struct
    type t = symbol
    let compare x y = compare x y
  end
);;

type univ = Univ0
	    | UnivVar of index
	    | UnivSucc of univ (* u < UnivSucc u *)
	    | UnivMax of univ * univ (* UnivMax u1 u2 >= u1 /\ UnivMax u1 u2 >= u2 *)
		
type position = Pos.t * Pos.t

let noposition = (Pos.none, Pos.none)

(* object are really usefull in order to manipulate Ocaml value from trep 
   but they cannot be compiled ...
*)

open Pprinter;;

class virtual ['a] tObj =
object 
  method uuid: int = 0
  method virtual get_name: string
  method virtual get_type: 'a
  method virtual pprint: unit -> token
  method virtual apply: 'a list -> 'a
end;;

type ('a, 'b) either = Left of 'a
		       | Right of 'b
;;

type term = Type of univ option
	    | Var of (name, index) either
	    | AVar of index option
	    | Cste of symbol
	    | Obj of term tObj
	    | Impl of quantifier * term
	    | Lambda of quantifier list * term
	    | Let of bool * (pattern * term) list * term
	    | Ifte of term * term * term
	    | App of term * arg list
	    | Case of term * equation list
	    (*| Where of term * declaration list*)

	    | TyAnnotation of term * tyAnnotation
	    | SrcInfo of term * position

and equation = Guarded of pattern * (guard * term) list
	       | NotGuarded of pattern * term

and pattern = PType of univ option
	      | PVar of name * term 
	      | PAVar of term
	      | PCste of symbol * term
	      | PAlias of name * pattern * term
	      | PApp of pattern * (pattern * nature) list * term

and nature = Explicit
	     | Hidden
	     | Implicit

and arg = term * nature

and quantifier = pattern list * tyAnnotation * nature

and guard = term

and tyAnnotation = NoAnnotation
		   | Infered of term
		   | Annotated of term

and declaration = Signature of symbol * term
		  | Equation of equation * (* where clause *) declaration list
		  | Inductive of name * quantifier list * term * (symbol * term) list
		  | RecordDecl of name * quantifier list * term * declaration list

  (* free variables (quantification level dependant) *)
  (* contains the type, and sum of substitution over the vars
     a fv can be pushed backward (for instance when qv is push):
       - all instance of the freevars are applied with the poped quantified variables
       - its type is quantified with Impl on the poped quantifier

     this feature allows to have typechecking conditional on providing the free variables
     (* through an interactive process reminiscent to proof mode *)

     FIXME: what to do of a free variable that is no more used ?
     
  *)
  (* list of declaration (quantification level dependant) 
     when pushing a quantifier, they are reinput in the term through the Where construction
  *)
  (* term stack & equation stack: used by the 
     typechecker to store terms/equations already typed, such that any further unification will apply on them
     this is the responsability of the typechecker to properly pop what he has pushed
     (TODO: have an helper function that check it)
  *)

  (* NB: I remove specific top level members for freevars, decls, ... *)
  (* rather than that we have an empty quantified frame (with a dummy pattern) at start time. c.f. init context *)

  (* need to input more proper info 
     tracking current levels of pushed vars (free and quantified)
  *)

(*

  ideas
  * for qvs
    - map: name -> index
    - map: index -> (term, name)
    - level: int which keep track of the next DeBruijn index for quantified vars
    - size: number of quantified vars
  * for fvs
    - level: int which keep track of the next DeBruijn index for free vars
    - size: number of free vars
    - map: index -> (term * term option)
  * for stacks:
    - for each element: a set of free variables (such that no need to always recompute if a substitution should be done)

  have hastbl in frames? --> empty_frame as a function: unit -> frame
  + summary in env ? map (what you want) (frame were it is)
  
*)

type frame = {

  qvs: (name * term) list; (* quantified variables *)
  pattern: pattern; (* the pattern initially pushed for the frame *)
  
  fvs: (term * term option) list; (* free variables *)
  
  (* stacks for different data *)
  decls: declaration list; (* for declaration *)
  terms: term list; (* for terms *)
  equations: equation list; (* for equation *)
  annotations: tyAnnotation list; (* for type annotation *)
  natures: nature list (* nature *)
  
}

let empty_frame = {
  qvs = [];
  pattern = PType (Some Univ0);
  fvs = [];
  decls = [];
  terms = [];
  equations = [];
  annotations = [];
  natures = [];
}

type env = 
{
  frames: frame list;
}

let empty_ctxt : env = {
  frames = [empty_frame]
};;

(*
  ADT for errors, an exception and a composition function
*)

type trep_error = AtPos of position * trep_error
		  | FreeError of string
		  | UnShiftable
		  | UnTypeckedTerm of term
;;

exception TrepException of trep_error
;;

