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

open Termeq;;

open Printf;;

open Extstate;;

open Char;;
open Map;;

module OrderedChar = 
    struct
      type t = Char.t
      let compare x y = Char.compare x y
    end;;

module CharMap = Map.Make(OrderedChar);; 

type charobj_state = {
  mutable defs: term CharMap.t; 
};;

let mchar_state : charobj_state = {
  
  defs = CharMap.empty; 

};;


(* First the Char *)

class charTypeObj =
object (self)
  inherit [term] pObj
  method get_name = "Char"
  method get_type = Type
  method pprint = (fun args _ -> self#get_name)
  method equal = (fun o -> (o#get_type = self#get_type && o#get_name = self#get_name))
  method my_self = (self :> term pObj)
  method exec = (fun args _ -> (Obj (self#my_self)))
  method show = (fun _ -> self#get_name)
end;;

let charType = 
  let o = new charTypeObj in
    Obj o#my_self
;;

class charTermObj c =
object (self)
  inherit [term] pObj
  val mutable charvalue = c
  method get_charvalue = charvalue
  method get_name = escaped charvalue
  method get_type = charType
  method equal = (fun o -> 
		    match (o#get_type, self#get_type) with
		      | (Obj ot, Obj mot) -> 
			  if (ot#equal mot) then
			    (((Obj.magic o) :> charTermObj)#get_charvalue = self#get_charvalue)
			  else
			    false
		      | _ -> false		    
		 )
  method pprint = (fun args _ -> String.concat "" ("'" :: (escaped self#get_charvalue) :: "'" :: []) )
  method my_self = (self :> term pObj)
  method exec = (fun args _ -> (Obj (self#my_self)))
  method show = (fun _ -> self#get_name)
end;;

let create_charTerm s =
  try (

    CharMap.find s mchar_state.defs

  ) with
    | _ -> (let o = new charTermObj s in
	    let t = Obj o#my_self in
	      mchar_state.defs <- CharMap.add s t mchar_state.defs;
	      t	      
	   )

;;


(* The class for the type *)

class stringTypeObj =
object (self)
  inherit [term] pObj
  method get_name = "String"
  method get_type = Type
  method pprint = (fun args _ -> self#get_name)
  method equal = (fun o -> (o#get_type = self#get_type && o#get_name = self#get_name))
  method my_self = (self :> term pObj)
  method exec = (fun args _ -> (Obj (self#my_self)))
  method show = (fun _ -> self#get_name)
end;;

let stringType = 
  let o = new stringTypeObj in
    Obj o#my_self
;;

(* The class for the term *)
class stringTermObj s =
object (self)
  inherit [term] pObj
  val mutable stringvalue = s
  method get_stringvalue = stringvalue
  method get_name = stringvalue
  method get_type = stringType
  method equal = (fun o -> 
		    match (o#get_type, self#get_type) with
		      | (Obj ot, Obj mot) -> 
			  if (ot#equal mot) then
			    (((Obj.magic o) :> stringTermObj)#get_stringvalue = self#get_stringvalue)
			  else
			    false
		      | _ -> false		    
		 )
  method pprint = (fun args _ -> String.concat "" ("\"" :: self#get_stringvalue :: "\"" :: []) )
  method my_self = (self :> term pObj)
  method exec = (fun args _ -> (Obj (self#my_self)))
  method show = (fun _ -> self#get_name)
end;;

let create_stringTerm s =
  let o = new stringTermObj s in
    Obj o#my_self
;;

(* The class for the term *)
class concatTermObj =
object (self)
  inherit [term] pObj
  method get_name = "stringConcat"
  method get_type = Forall ("H0", stringType, Forall ("H0", stringType, stringType)) 
  method equal = (fun o -> 
		    self#get_name = o#get_name
		 )
  method pprint = (fun args implicite -> 
		     String.concat "" ("stringConcat " :: (string_of_listterm args implicite) :: [])
		  )
  method my_self = (self :> term pObj)
  method exec = (fun args def ->
		   match args with
		     | (Obj o1) :: (Obj o2) :: [] -> (
			 
			 let o1 = ((Obj.magic o1) :> stringTermObj) in
			 let o2 = ((Obj.magic o2) :> stringTermObj) in
			   create_stringTerm (String.concat "" [o1#get_stringvalue; o2#get_stringvalue])
		       )       
		     | a -> App (Obj self#my_self, a)
			 
		)
  method show = (fun _ -> self#get_name)
end;;

let create_stringconcat =
  let o = new concatTermObj in
    Obj o#my_self
;;


let mstring_init =

  add_def "StdLib.string.String" stringType Type TYPE ext_typechecker_state ext_typechecker_state;

  add_def "StdLib.string.Char" charType Type TYPE ext_typechecker_state ext_typechecker_state;

  let o = new concatTermObj in
    add_def "StdLib.string.stringConcat" (Obj o#my_self) o#get_type FUNCTION ext_typechecker_state ext_typechecker_state;


;;
