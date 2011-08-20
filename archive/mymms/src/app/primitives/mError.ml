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
open Extstate;;
open State;;
open String;;
open Simpl;;
open Varmap;;
open Big_int;;
open Definition;;
open Term;;
open Command;;

open Mstring;;

open Termeq;;


(****************************)

(* The class for the type *)

(* The class for the term *)
class mErrorObj =
object (self)
  inherit [term] pObj
  val mutable err = ""
  method get_name = "error"    
  method get_type = Forall ("A", Type, Forall ("s", stringType, Var "A"))
  method equal = (fun o -> false)
  method pprint = (fun args _ -> self#get_name)
  method my_self = (self :> term pObj)
  method exec = (fun args _ -> 
		   match args with
		     | (Obj o1) :: (Obj o2) ::[] -> (
			 let o2 = ((Obj.magic o2) :> stringTermObj) in
			   err <- o2#get_stringvalue;
			   (Obj (self#my_self))
		       )       
		     | a -> App (Obj self#my_self, a)
		)
    
  method show = (fun _ -> String.concat " " [self#get_name; ] )  
end;;



let mError_init =

  let o = new mErrorObj in  
    add_def "StdLib.Error.error" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let _ = add_implicite "StdLib.Error.error" 1 ext_typechecker_state ext_typechecker_state in
    ()
;;
