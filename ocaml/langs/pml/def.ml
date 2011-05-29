open Printf;;

(* Language definition *)

type kind = KStar (* notation := * *)
	    | KImpl of (kind * kind) (* notation := -> *)

type mltype = TyVar of string (* :: KStar *)
	      | TyCste of string
	      | Unit | Int of int | Double | Float | Bool (* :: * *)
	      | Array of int | TyImpl | TyRef (* :: * -> * *)
	      | TyApp (* :: ( * -> k ) -> k *)

(* for now no wf inductive types ... 
   defined as type / fct axioms
   ex:

list :: * -> *
(:) :: a -> list a -> list a
[[]] :: list a

*)

type typeclass_quantification = string (* class name *) * string (* TyVar *)

type signature = typeclass_quantification list * mltype

type index = int

type name = string

type property = Pure | Impure (* act as a check *)
		| Deterministic | Nondeterministic (* act on the semantic *)
		| Associativity | Priority

type term = Var of index
	    | AVar
	    | Cste of name
	    | Alias of name * term
	    | App of term * term list
	    | Let of bool (* rec ? *) * (pattern * term) list * term
	    | Lambda of pattern list * term
	    | Case of term * equation list
	    | Ifte of term * term * term
	    | Where of term * term_declaration list

	    | TeRef of term
	    | Assign of term * term
	    | Seq of term * term
	    | While of term * term
	    | If of term * term

	    | BackTrack of term (* == id for a deteministic term *)
	    | Spawn of term (* only work if the term is pure, (id on impure one) *)

and pattern = term

and equation = (term * guard list) list * term

and guard = term

and term_declaration = TeSignature of name * property list * signature
		       | TeDef of equation

type type_declaration = name * kind

type typeclass_declaration = name * string (* type var *) * kind * term_declaration list

type typeclass_instance = typeclass_quantification list * name * mltype * term_declaration list

type declaration = TermDecl of term_declaration 
		   | TypeDecl of type_declaration
		   | TypeClassDecl of typeclass_declaration
		   | TypeClassInstance of typeclass_instance

type code = name * declaration list

