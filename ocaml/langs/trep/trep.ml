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


type sourceLocation = string option * (int * int) * (int * int);;

type definitionId = string array * string

type property = Associativity of associativity
		| Precedence of precedence
		| Pure | Impure
		| Deterministic | NonDeterministic
		| Partial | Complete
		| StructuralTermination of int array
		| Constructor | Inductive
		| ModuleImpl | ModuleSig
		| WellFormed

type term = Type of univ_level
	    | Var of name * index option
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

and definition = Declaration of name * property array * quantifier array (* args (bind the name in where) *) * term (* reminiscent signature *) * equation array (* definitions *) * definition array (* with *)
		 | Definition of name * property array * quantifier array (* args (bind the name in where) *) * term (* reminiscent signature *) * equation array (* definitions *) * definition array (* where *)
(*

(=) {A: Type} (a: Type) :: A -> Type : noassoc, prio 50, inductive
   with
     eqrefl :: a = a

(*
eqrefl :: {A :: Type} -> {a :: Type} -> a = a
*)

Eq (A:: Type) :: Type
  with
    (==):: A -> A -> Bool

(*
(==) :: {A:: Type} -> [Eq A] -> A -> A -> Bool
*)

Ord (A:: Type) :: Type
   with

     Ordering :: Type
        with
          EQ :: Ordering
          LT :: Ordering
          GT :: Ordering

     compare :: A -> A -> Ordering
     
     (<) :: A -> A -> Bool
       where
         x < y := case compare x y of
                    | LT := True
                    | _ := False

     (>) :: A -> A -> Bool
       where
         x < y := case compare x y of
                    | GT := True
                    | _ := False

     EqA :: Eq A
       where
          x == y := case compare x y of
                      | EQ := True
                      | _ := False

(*
Ordering :: Type
compare :: {A :: Type} -> [Ord A] -> A -> A -> Ordering
(<) :: {A :: Type} -> [Ord A] -> A -> A -> Bool
(>) :: {A :: Type} -> [Ord A] -> A -> A -> Bool
EqA :: {A :: Type} -> [Ord A] -> Eq A
*)

Bool :: Type
  with 
    True :: Bool
    False :: Bool
  

    [~) :: Bool -> Bool
      where
        ~ True := False
        ~ False := True

(*
  [~) :: Bool -> Bool
*)

EqBool :: Eq Bool
  where
    True == True := True
    False == False := True

max :: {A :: Type} -> [Ord A] -> A -> A -> A
  where
    max {A} [H] x y = if x < y then y else x

*)






