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

open Term;;

open Termeq;;


(****************************)

(* The class for the type *)

class mMutableTypeObj =
object (self)
  inherit [term] pObj
  method get_name = "Mutable"
  method get_type = Forall ("A", Type, Type)
  method pprint = (fun args _ -> self#get_name)
  method equal = (fun o -> (o#get_type = self#get_type && o#get_name = self#get_name))
  method my_self = (self :> term pObj)
  method exec = (fun args _ -> (Obj (self#my_self)))
  method show = (fun _ -> self#get_name)
end;;

let mMutableType = 
  let o = new mMutableTypeObj in
    Obj o#my_self
;;

(* The class for the term *)
class mMutableTermObj te ty =
object (self)
  inherit [term] pObj
  val mutable value : term = te
  val mutable typ = App (mMutableType, ty::[])
  method get_value = value
  method set_value te = (value <- te)
  method get_name = String.concat "" ("{0x" :: (string_of_int (((Obj.magic self) :> int))) :: "}" :: [])
  method get_type = typ
  method equal = (fun o -> false)
  method pprint = (fun args _ -> self#get_name)
  method my_self = (self :> term pObj)
  method exec = (fun args _ -> (Obj (self#my_self)))
  method show = (fun _ -> self#get_name)  
end;;

let create_mMutableTerm te ty =
  let o = new mMutableTermObj te ty in
    Obj o#my_self
;;


(* The class for the term *)
class mCreateMutableTermObj =
object (self)
  inherit [term] pObj
  method get_name = "CreateMutable"
  method get_type = Forall ("A", Type, Forall ("x", Var "A", App (mMutableType, (Var "A")::[])))
  method equal = (fun o -> false)
  method pprint = (fun args _ -> self#get_name)
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match simpl_listterm args def with
      | hd1 :: hd2 :: [] -> (

	  create_mMutableTerm hd1 hd2
            
        )       
      | a -> App (Obj self#my_self, a)
	  

  )
  method show = (fun _ -> self#get_name)  
end;;


(* The class for the term *)
class mGetMutableTermObj =
object (self)
  inherit [term] pObj
  method get_name = "GetMutable"
  method get_type = Forall ("A", Type, Forall ("H", App (mMutableType, (Var "A")::[]), Var "A"))
  method equal = (fun o -> false)
  method pprint = (fun args _ -> self#get_name)
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match simpl_listterm args def with
      | hd1 :: Obj o :: [] -> (

	  let o = ((Obj.magic o) :> mMutableTermObj) in
	    o#get_value
            
        )       
      | a -> App (Obj self#my_self, a)
	  

  )
  method show = (fun _ -> self#get_name)  
end;;

(* The class for the term *)
class mSetMutableTermObj =
object (self)
  inherit [term] pObj
  method get_name = "GetMutable"
  method get_type = Forall ("A", Type, Forall ("H", App (mMutableType, (Var "A")::[]), Forall ("H0", Var "A", Var "A")))
  method equal = (fun o -> false)
  method pprint = (fun args _ -> self#get_name)
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match simpl_listterm args def with
      | hd1 :: Obj o :: hd2 :: [] -> (

	  let o = ((Obj.magic o) :> mMutableTermObj) in
	    o#set_value hd2;
	    hd2
            
        )       
      | a -> App (Obj self#my_self, a)
	  

  )
  method show = (fun _ -> self#get_name)  
end;;

let mutable_init =

  add_def "StdLib.Mutable.Mutable" mMutableType Type TYPE ext_typechecker_state ext_typechecker_state;

  let o = new mCreateMutableTermObj in  
    add_def "StdLib.Mutable.CreateMutable" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mGetMutableTermObj in  
    add_def "StdLib.Mutable.GetMutable" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mSetMutableTermObj in  
    add_def "StdLib.Mutable.SetMutable" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

;;
