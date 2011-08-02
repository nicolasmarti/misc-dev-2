(*
  This file is part of Mymms.

  Mymms is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  Mymms is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with Mymms.  If not, see <http://www.gnu.org/licenses/>.

  Copyright (C) 2008 Nicolas Marti
*)

open List;;
open String;;
open Varset;;
open Varmap;;
open String;;
open Definition;;

type implicite = (int VarMap.t)
;;

type nature =
  | DATA
  | FUNCTION
  | TYPE
  | UNKNOWN
;;

class virtual ['a] pObj =
object 
  method uuid: int = 0
  method virtual get_name: string
  method virtual get_type: 'a
  method virtual equal: 'a pObj -> bool
  method virtual pprint: 'a list -> implicite -> string
  method virtual exec: 'a list -> ('a * 'a * nature) objdef -> 'a
  method virtual show: implicite -> string
end;;

type name = string;;

type term =
    | Type
    | Cste of name
    | Obj of term pObj
    | Var of var
    | Let of (var * term * term)
    | Lambda of var * term * term
    | Forall of var * term * term
    | Phi of var * (var * term) list * term * (int list) option * term
    | Ind of var * (var * term) list * term * term list
    | App of term * term list
	
    (* term to destruct, list of destructors, returned type, destruct inductive type *)	
    | Match of term * (term list) * (term  option) * (term option)
    | Cons of int * term

    (* Term only valid pre-termchecking *)
	
    (* Advanced Match *)
    | AdvMatch  of term * (term * term) list * term option

    (* anonymous var *) 
    | Avar

;;

type context = (var * term) list
;;

(*The new definition (copied in definition.ml)*)

type definition = (term * term * nature) objdef
;;

type overload = ((term * int) list) VarMap.t
;;

type oracles = (context -> term -> definition -> term) list
;;

type coercion = (term * term) list
;;


type subst =
  | Mgu of (var * term) list
  | DnkMgu
  | NoMgu
;;

type 'a return =
  | Ok of 'a
  | Error of string list
;;

