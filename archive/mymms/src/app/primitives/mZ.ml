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
open MQ;;
open Num;;

open Termeq;;


(****************************)

(* The class for the type *)

class mZTypeObj =
object (self)
  inherit [term] pObj
  method get_name = "Z"
  method get_type = Type
  method pprint = (fun args _ -> self#get_name)
  method equal = (fun o -> (o#get_type = self#get_type && o#get_name = self#get_name))
  method my_self = (self :> term pObj)
  method exec = (fun args _ -> (Obj (self#my_self)))
  method show = (fun _ -> self#get_name)
end;;

let mZType = 
  let o = new mZTypeObj in
    Obj o#my_self
;;

(* The class for the term *)
class mZTermObj n =
object (self)
  inherit [term] pObj
  val mutable value = n
  method get_value = value
  method get_name = string_of_big_int value
  method get_type = mZType
  method equal = (fun o -> 
		    match (o#get_type, self#get_type) with
		      | (Obj ot, Obj mot) -> 
			  if (ot#equal mot) then
			    (eq_big_int ((Obj.magic o) :> mZTermObj)#get_value self#get_value)
			  else
			    false
		      | _ -> false		    
		 )
  method pprint = (fun args _ -> self#get_name)
  method my_self = (self :> term pObj)
  method exec = (fun args _ -> (Obj (self#my_self)))
  method show = (fun _ -> self#get_name)
end;;

let create_mZTerm n =
  let o = new mZTermObj n in
    Obj o#my_self
;;

(* The classes for the basic functions *)

(* Addition *)
class mZPlusTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "QPlus"
  method get_type = Forall ("H0", mZType, Forall ("H0", mZType, mZType))
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " + " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("ZPlus " :: (string_of_listterm args implicite) :: [])
  )
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mZTermObj) in
          let o2 = ((Obj.magic o2) :> mZTermObj) in
            create_mZTerm (add_big_int o1#get_value o2#get_value)
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mZPlusTerm =
  let o = new mZPlusTermObj in
    Obj o#my_self
;;

(* substraction *)
class mZMinusTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "ZMinus"
  method get_type = Forall ("H0", mZType, Forall ("H0", mZType, mZType))
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " - " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("ZMinus " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mZTermObj) in
          let o2 = ((Obj.magic o2) :> mZTermObj) in
            create_mZTerm (sub_big_int o1#get_value o2#get_value)
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mZMinusTerm =
  let o = new mZMinusTermObj in
    Obj o#my_self
;;

(* multiplication *)
class mZMultiplyTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "ZMultiply"
  method get_type = Forall ("H0", mZType, Forall ("H0", mZType, mZType))
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " * " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("ZMultiply " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mZTermObj) in
          let o2 = ((Obj.magic o2) :> mZTermObj) in
            create_mZTerm (mult_big_int o1#get_value o2#get_value)
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mZMultiplyTerm =
  let o = new mZMultiplyTermObj in
    Obj o#my_self
;;

(* division *)
class mZDivideTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "ZDivide"
  method get_type = Forall ("H0", mZType, Forall ("H0", mZType, mZType))
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " / " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("ZDivide " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mZTermObj) in
          let o2 = ((Obj.magic o2) :> mZTermObj) in
	    create_mZTerm (div_big_int o1#get_value o2#get_value)
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mZDivideTerm =
  let o = new mZDivideTermObj in
    Obj o#my_self
;;

(* equality *)
class mZEqTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "ZEq"
  method get_type = Forall ("H0", mZType, Forall ("H0", mZType, Cste "bool"))
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " == " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("ZEq " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mZTermObj) in
          let o2 = ((Obj.magic o2) :> mZTermObj) in
            if (eq_big_int o1#get_value o2#get_value) then
	      Cste "true"
	    else
	      Cste "false"
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mZEqTerm =
  let o = new mZEqTermObj in
    Obj o#my_self
;;

(* Less than  *)
class mZLtTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "ZLt"
  method get_type = Forall ("H0", mZType, Forall ("H0", mZType, Cste "bool"))
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " < " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("ZLt " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mZTermObj) in
          let o2 = ((Obj.magic o2) :> mZTermObj) in
            if (lt_big_int o1#get_value o2#get_value) then
	      Cste "true"
	    else
	      Cste "false"
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mZLtTerm =
  let o = new mZLtTermObj in
    Obj o#my_self
;;

(* Less or equal  *)
class mZLteTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "ZLte"
  method get_type = Forall ("H0", mZType, Forall ("H0", mZType, Cste "bool"))
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " <= " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("ZLte " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mZTermObj) in
          let o2 = ((Obj.magic o2) :> mZTermObj) in
            if (le_big_int o1#get_value o2#get_value) then
	      Cste "true"
	    else
	      Cste "false"
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mZLteTerm =
  let o = new mZLteTermObj in
    Obj o#my_self
;;

(* Greater than  *)
class mZGtTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "ZGt"
  method get_type = Forall ("H0", mZType, Forall ("H0", mZType, Cste "bool"))
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " > " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("ZGt " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mZTermObj) in
          let o2 = ((Obj.magic o2) :> mZTermObj) in
            if (gt_big_int o1#get_value o2#get_value) then
	      Cste "true"
	    else
	      Cste "false"
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mZGtTerm =
  let o = new mZGtTermObj in
    Obj o#my_self
;;

(* Greater than  *)
class mZGteTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "ZGte"
  method get_type = Forall ("H0", mZType, Forall ("H0", mZType, Cste "bool"))
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " >= " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("ZGte " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mZTermObj) in
          let o2 = ((Obj.magic o2) :> mZTermObj) in
            if (ge_big_int o1#get_value o2#get_value) then
	      Cste "true"
	    else
	      Cste "false"
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mZGteTerm =
  let o = new mZGteTermObj in
    Obj o#my_self
;;

(* Conversion *)

class mZ2QTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "Z2Q"
  method get_type = Forall ("H0", mZType, mQType)
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1 :: [] ->
          (string_of_term hd1 implicite)

      | _ -> concat "" ("Z2Q " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: [] -> (

          let o1 = ((Obj.magic o1) :> mZTermObj) in
            create_mQTerm (num_of_big_int o1#get_value)
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mZ2QTerm =
  let o = new mZ2QTermObj in
    Obj o#my_self
;;

let mZ_init =

  add_def "StdLib.Z.Z" mZType Type TYPE ext_typechecker_state ext_typechecker_state;

  let o = new mZPlusTermObj in  
    add_def "StdLib.Z.Zplus" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mZMinusTermObj in  
    add_def "StdLib.Z.Zminus" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mZMultiplyTermObj in  
    add_def "StdLib.Z.Zmultiply" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mZDivideTermObj in  
    add_def "StdLib.Z.Zdivide" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mZEqTermObj in  
    add_def "StdLib.Z.Zeq" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mZLtTermObj in  
    add_def "StdLib.Z.Zlt" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mZLteTermObj in  
    add_def "StdLib.Z.Zle" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mZGtTermObj in  
    add_def "StdLib.Z.Zgt" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mZGteTermObj in  
    add_def "StdLib.Z.Zge" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  add_coercion mZ2QTerm (Forall ("H0", mZType, mQType)) ext_typechecker_state ext_typechecker_state



;;
