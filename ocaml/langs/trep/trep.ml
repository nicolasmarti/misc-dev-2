(*
 
 This file is free software: you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation, either version 3 of the License, or
 (at your option) any later version.
 
 This file is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.
 
 You should have received a copy of the GNU General Public License
 along with this file.  If not, see <http://www.gnu.org/licenses/>.
 
 Copyright (C) Nicolas Marti
*)

(* 
Definition of AST
*)

open Universe;;
open Array;;

type name = string;;

(*
  >= 0 -> quantified variable
  < 0 -> free variable
*)
type index = int;;

type nature = Explicit (* ( ... ) *)
	      | Hidden (* { ... } *)
	      | Implicit (* [ ... ] *)


type sourceLocation = name option * (int * int) * (int * int);;

type property = Associativity of associativity
		| Precedence of precedence
		| Pure
		| Impure
		| Deterministic
		| NonDeterministic
		| Partial
		| Complete
		| StructuralTermination of int array
		| StrictlyPositive
		| Constructor

type term = Type of univ_level
	    | Var of name * index 
	    | AVar of index
	    | Cste of name
	    | Alias of name * term
	    | Let of (pattern * term) array * term
	    | Impl of quantifier * term
	    | Case of term * equation array
	    | Ifte of term * term * term
	    | App of term * quantifier
	    | Op of name

and typeannotation = NoTypeAnnotation
		     | Inferred of term
		     | Annotation of term

and quantifier = nature * pattern * typeannotation

and pattern = term

and equation = (pattern * guard array) array (* := l.h.s *) * term (* := r.h.s *) * definition array (* where *)

and guard = term

and definition = name * property array * term (* signature *) * equation array (* definitions *) * definition array (* where *)





