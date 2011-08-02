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

open Printf;;
open Def;;
open String;;
open Printer;;
open Llvm;;
open Varmap;;
open Jitinit;;

(* the term te must be app_nf *)

let rec compile te ty =
  match te with
    | Var v -> 
	(try 
	   let (m_llvalue, m_type) = Hashtbl.find named_values v in
	     m_llvalue
	 with
             | Not_found -> raise (Error 
				     (concat "" ("unknown variable name: " :: v :: []))
				  )
	)

    |_ -> 
       raise (Error 
		
		(concat "" ("do not now how to compile: " :: (string_of_term te VarMap.empty) :: []))
	     )
;;
