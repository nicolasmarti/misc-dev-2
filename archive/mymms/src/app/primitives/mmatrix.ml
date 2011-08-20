(*
  This file is part of Mymms.

  Mymms is free software: you can redistribool it and/or modify
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

open Def;;
open Printer;;
open State;;
open String;;
open Simpl;;
open Varmap;;
open MN;;
open Extstate;;


(* The class for the type *)

class mmatrixTypeObj =
object (self)
  inherit [term] pObj
  method get_name = "Matrix"
  method get_type = Forall ("A", Type, Forall ("n", mNType, Forall ("m", mNType, Type)))
  method pprint = (fun args implicite -> 
		     concat "" (self#get_name :: (string_of_listterm2 args implicite) :: [])
		  )
  method equal = (fun o -> (o#get_type = self#get_type && o#get_name = self#get_name))
  method my_self = (self :> term pObj)
  method exec = (fun args _ -> (Obj (self#my_self)))
  method show = (fun _ -> self#get_name)
end;;

let mmatrixType = 
  let o = new mmatrixTypeObj in
    Obj o#my_self
;;

let mmatrix_init =
  
      add_def "StdLib.matrix.Matrix" mmatrixType Type TYPE ext_typechecker_state ext_typechecker_state

;;
