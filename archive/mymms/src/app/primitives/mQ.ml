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
open Num;;
open Definition;;
open Termeq;;

(* float to num *)

let scaling_factor = Num.power_num (Num.Int 10) (Num.Int 16)

let mQ_of_float f =
  let mQ_of_positive_float f =
    let m, e = frexp f in
    let sm = string_of_float m in
    let s = String.make 16 '0' in
    String.blit sm 2 s 0 (String.length sm - 2);
    let e' = Num.power_num (Num.Int 2) (Num.num_of_int e) in
    Num.div_num (Num.mult_num (Num.num_of_string s) e') scaling_factor
  in
  if f = 0.0 then Num.Int 0
  else if f < 0.0 then
    let num = mQ_of_positive_float (abs_float f) in
      Num.minus_num num
  else mQ_of_positive_float f
;;

(****************************)

(* The class for the type *)

class mQTypeObj =
object (self)
  inherit [term] pObj
  method get_name = "Q"
  method get_type = Type
  method pprint = (fun args _ -> self#get_name)
  method equal = (fun o -> (o#get_type = self#get_type && o#get_name = self#get_name))
  method my_self = (self :> term pObj)
  method exec = (fun args _ -> (Obj (self#my_self)))
  method show = (fun _ -> self#get_name)
end;;

let mQType = 
  let o = new mQTypeObj in
    Obj o#my_self
;;

(* The class for the term *)
class mQTermObj n =
object (self)
  inherit [term] pObj
  val mutable value = n
  method get_value = value
  method get_name = string_of_num value
  method get_type = mQType
  method equal = (fun o -> 
		    match (o#get_type, self#get_type) with
		      | (Obj ot, Obj mot) -> 
			  if (ot#equal mot) then
			    (((Obj.magic o) :> mQTermObj)#get_value =/ self#get_value)
			  else
			    false
		      | _ -> false		    
		 )
  method pprint = (fun args _ -> self#get_name)
  method my_self = (self :> term pObj)
  method exec = (fun args _ -> (Obj (self#my_self)))
  method show = (fun _ -> self#get_name)
end;;

let create_mQTerm n =
  let o = new mQTermObj n in
    Obj o#my_self
;;

(* The classes for the basic functions *)

(* Addition *)
class mQPlusTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "QPlus"
  method get_type = Forall ("H0", mQType, Forall ("H0", mQType, mQType))
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " + " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("QPlus " :: (string_of_listterm args implicite) :: [])
  )
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mQTermObj) in
          let o2 = ((Obj.magic o2) :> mQTermObj) in
            create_mQTerm (o1#get_value +/ o2#get_value)
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mQPlusTerm =
  let o = new mQPlusTermObj in
    Obj o#my_self
;;

(* substraction *)
class mQMinusTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "QMinus"
  method get_type = Forall ("H0", mQType, Forall ("H0", mQType, mQType))
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " - " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("QMinus " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mQTermObj) in
          let o2 = ((Obj.magic o2) :> mQTermObj) in
            create_mQTerm (o1#get_value -/ o2#get_value)
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mQMinusTerm =
  let o = new mQMinusTermObj in
    Obj o#my_self
;;

(* multiplication *)
class mQMultiplyTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "QMultiply"
  method get_type = Forall ("H0", mQType, Forall ("H0", mQType, mQType))
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " * " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("QMultiply " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mQTermObj) in
          let o2 = ((Obj.magic o2) :> mQTermObj) in
            create_mQTerm (o1#get_value */ o2#get_value)
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mQMultiplyTerm =
  let o = new mQMultiplyTermObj in
    Obj o#my_self
;;

(* division *)
class mQDivideTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "QDivide"
  method get_type = Forall ("H0", mQType, Forall ("H0", mQType, mQType))
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " / " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("QDivide " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mQTermObj) in
          let o2 = ((Obj.magic o2) :> mQTermObj) in
            create_mQTerm (o1#get_value // o2#get_value)
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mQDivideTerm =
  let o = new mQDivideTermObj in
    Obj o#my_self
;;

(* equality *)
class mQEqTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "QEq"
  method get_type = Forall ("H0", mQType, Forall ("H0", mQType, Cste "bool"))
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " == " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("QEq " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mQTermObj) in
          let o2 = ((Obj.magic o2) :> mQTermObj) in
            if (o1#get_value =/ o2#get_value) then
	      Cste "true"
	    else
	      Cste "false"
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mQEqTerm =
  let o = new mQEqTermObj in
    Obj o#my_self
;;

(* Less than  *)
class mQLtTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "QLt"
  method get_type = Forall ("H0", mQType, Forall ("H0", mQType, Cste "bool"))
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " < " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("QLt " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mQTermObj) in
          let o2 = ((Obj.magic o2) :> mQTermObj) in
            if (o1#get_value </ o2#get_value)  then
	      Cste "true"
	    else
	      Cste "false"
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mQLtTerm =
  let o = new mQLtTermObj in
    Obj o#my_self
;;

(* Less or equal  *)
class mQLteTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "QLte"
  method get_type = Forall ("H0", mQType, Forall ("H0", mQType, Cste "bool"))
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " <= " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("QLte " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mQTermObj) in
          let o2 = ((Obj.magic o2) :> mQTermObj) in
            if (o1#get_value <=/ o2#get_value) then
	      Cste "true"
	    else
	      Cste "false"
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mQLteTerm =
  let o = new mQLteTermObj in
    Obj o#my_self
;;

(* Greater than  *)
class mQGtTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "QGt"
  method get_type = Forall ("H0", mQType, Forall ("H0", mQType, Cste "bool"))
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " > " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("QGt " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mQTermObj) in
          let o2 = ((Obj.magic o2) :> mQTermObj) in
            if (o1#get_value >/ o2#get_value) then
	      Cste "true"
	    else
	      Cste "false"
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mQGtTerm =
  let o = new mQGtTermObj in
    Obj o#my_self
;;

(* Greater than  *)
class mQGteTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "QGte"
  method get_type = Forall ("H0", mQType, Forall ("H0", mQType, Cste "bool"))
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " >= " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("QGte " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mQTermObj) in
          let o2 = ((Obj.magic o2) :> mQTermObj) in
            if (o1#get_value >=/ o2#get_value) then
	      Cste "true"
	    else
	      Cste "false"
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mQGteTerm =
  let o = new mQGteTermObj in
    Obj o#my_self
;;


let mQ_init =

  add_def "StdLib.Q.Q" mQType Type TYPE ext_typechecker_state ext_typechecker_state;

  let o = new mQPlusTermObj in  
    add_def "StdLib.Q.Qplus" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mQMinusTermObj in  
    add_def "StdLib.Q.Qminus" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mQMultiplyTermObj in  
    add_def "StdLib.Q.Qmultiply" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mQDivideTermObj in  
    add_def "StdLib.Q.Qdivide" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mQEqTermObj in  
    add_def "StdLib.Q.Qeq" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mQLtTermObj in  
    add_def "StdLib.Q.Qlt" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mQLteTermObj in  
    add_def "StdLib.Q.Qle" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mQGtTermObj in  
    add_def "StdLib.Q.Qgt" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mQGteTermObj in  
    add_def "StdLib.Q.Qge" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

;;
