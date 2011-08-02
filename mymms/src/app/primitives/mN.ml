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

open MZ;;
open Num;;
open Mstring;;
open Termeq;;


(****************************)

(* The class for the type *)

class mNTypeObj =
object (self)
  inherit [term] pObj
  method get_name = "N"
  method get_type = Type
  method pprint = (fun args _ -> self#get_name)
  method equal = (fun o -> (o#get_type = self#get_type && o#get_name = self#get_name))
  method my_self = (self :> term pObj)
  method exec = (fun args _ -> (Obj (self#my_self)))
  method show = (fun _ -> self#get_name)
end;;

let mNType = 
  let o = new mNTypeObj in
    Obj o#my_self
;;

(* The class for the term *)
class mNTermObj n =
object (self)
  inherit [term] pObj
  val mutable value = n
  method get_value = value
  method get_name = string_of_big_int value
  method get_type = mNType
  method equal = (fun o -> 
		    match (o#get_type, self#get_type) with
		      | (Obj ot, Obj mot) -> 
			  if (ot#equal mot) then
			    (eq_big_int ((Obj.magic o) :> mNTermObj)#get_value self#get_value)
			  else
			    false
		      | _ -> false		    
		 )
  method pprint = (fun args _ -> self#get_name)
  method my_self = (self :> term pObj)
  method exec = (fun args _ -> (Obj (self#my_self)))
  method show = (fun _ -> self#get_name)  
end;;

let create_mNTerm n =
  let o = new mNTermObj n in
    Obj o#my_self
;;

(* The classes for the basic functions *)

(* Addition *)
class mNPlusTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "NPlus"
  method get_type = Forall ("H0", mNType, Forall ("H0", mNType, mNType))
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " + " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("NPlus " :: (string_of_listterm args implicite) :: [])
  )
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mNTermObj) in
          let o2 = ((Obj.magic o2) :> mNTermObj) in
            create_mNTerm (add_big_int o1#get_value o2#get_value)
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mNPlusTerm =
  let o = new mNPlusTermObj in
    Obj o#my_self
;;

(* substraction (* in Z *) *)
class mNMinusZTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "NMinusZ"
  method get_type = Forall ("H0", mNType, Forall ("H0", mNType, mZType))
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " - " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("NMinusZ " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mNTermObj) in
          let o2 = ((Obj.magic o2) :> mNTermObj) in
            create_mZTerm (sub_big_int o1#get_value o2#get_value)
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mNMinusZTerm =
  let o = new mNMinusZTermObj in
    Obj o#my_self
;;

(* substraction (* in N *) *)
class mNMinusNTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "NMinusN"
  method get_type = Forall ("H0", mNType, Forall ("H0", mNType, mNType))
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " - " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("NMinusN " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mNTermObj) in
          let o2 = ((Obj.magic o2) :> mNTermObj) in
            create_mNTerm (
	      
	      max_big_int
		(sub_big_int o1#get_value o2#get_value)
		zero_big_int

	    )
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mNMinusNTerm =
  let o = new mNMinusNTermObj in
    Obj o#my_self
;;

(* multiplication *)
class mNMultiplyTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "NMultiply"
  method get_type = Forall ("H0", mNType, Forall ("H0", mNType, mNType))
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " * " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("NMultiply " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mNTermObj) in
          let o2 = ((Obj.magic o2) :> mNTermObj) in
            create_mNTerm (mult_big_int o1#get_value o2#get_value)
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mNMultiplyTerm =
  let o = new mNMultiplyTermObj in
    Obj o#my_self
;;

(* multiplication *)
class mNDivideTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "NDivide"
  method get_type = Forall ("H0", mNType, Forall ("H0", mNType, mNType))
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " / " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("NDivide " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mNTermObj) in
          let o2 = ((Obj.magic o2) :> mNTermObj) in
            create_mNTerm (div_big_int o1#get_value o2#get_value)
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mNDivideTerm =
  let o = new mNDivideTermObj in
    Obj o#my_self
;;

(* equality *)
class mNEqTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "NEq"
  method get_type = Forall ("H0", mNType, Forall ("H0", mNType, Cste "bool"))
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " == " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("NEq " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mNTermObj) in
          let o2 = ((Obj.magic o2) :> mNTermObj) in
            if (eq_big_int o1#get_value o2#get_value) then
	      Cste "StdLib.Bool.true"
	    else
	      Cste "StdLib.Bool.false"
        )       
      | a -> App (Obj self#my_self, a)

  )
  method show = (fun _ -> self#get_name)
end;;

let mNEqTerm =
  let o = new mNEqTermObj in
    Obj o#my_self
;;

(* Less than  *)
class mNLtTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "NLt"
  method get_type = Forall ("H0", mNType, Forall ("H0", mNType, Cste "bool"))
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " < " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("NLt " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mNTermObj) in
          let o2 = ((Obj.magic o2) :> mNTermObj) in
            if (lt_big_int o1#get_value o2#get_value) then
	      Cste "true"
	    else
	      Cste "false"
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mNLtTerm =
  let o = new mNLtTermObj in
    Obj o#my_self
;;

(* Less or equal  *)
class mNLteTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "NLte"
  method get_type = Forall ("H0", mNType, Forall ("H0", mNType, Cste "bool"))
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " <= " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("NLte " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mNTermObj) in
          let o2 = ((Obj.magic o2) :> mNTermObj) in
            if (le_big_int o1#get_value o2#get_value) then
	      Cste "true"
	    else
	      Cste "false"
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mNLteTerm =
  let o = new mNLteTermObj in
    Obj o#my_self
;;

(* Greater than  *)
class mNGtTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "NGt"
  method get_type = Forall ("H0", mNType, Forall ("H0", mNType, Cste "bool"))
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " > " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("NGt " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mNTermObj) in
          let o2 = ((Obj.magic o2) :> mNTermObj) in
            if (gt_big_int o1#get_value o2#get_value) then
	      Cste "true"
	    else
	      Cste "false"
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mNGtTerm =
  let o = new mNGtTermObj in
    Obj o#my_self
;;

(* Greater than  *)
class mNGteTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "NGte"
  method get_type = Forall ("H0", mNType, Forall ("H0", mNType, Cste "bool"))
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " >= " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("NGte " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> mNTermObj) in
          let o2 = ((Obj.magic o2) :> mNTermObj) in
            if (ge_big_int o1#get_value o2#get_value) then
	      Cste "true"
	    else
	      Cste "false"
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mNGteTerm =
  let o = new mNGteTermObj in
    Obj o#my_self
;;

(* Conversion *)

class mN2ZTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "N2Z"
  method get_type = Forall ("H0", mNType, mZType)
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1 :: [] ->
          (string_of_term hd1 implicite)

      | _ -> concat "" ("N2Z " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: [] -> (

          let o1 = ((Obj.magic o1) :> mNTermObj) in
            create_mZTerm o1#get_value
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mN2ZTerm =
  let o = new mN2ZTermObj in
    Obj o#my_self
;;

(* fold_left *)

let rec nfoldleft start stop step f a def =
  if (gt_big_int start stop) then
    a
  else
    let comp = (App (f, a :: (create_mNTerm start) :: [])) in
      nfoldleft (add_big_int start step) stop step f comp def

;;


class nFoldLeftTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "NFoldLeft"
  method get_type = 
    let largs = ("A", Type) :: ("start", mNType) :: ("stop", mNType) :: ("step", mNType) :: ("f", Forall ("x", Var "A", Forall ("y", mNType, Var "A"))) :: ("a", Var "A") :: [] in
      largs_foralls (Var "A") largs      
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1 :: hd2 :: hd3 :: hd4 :: hd5 :: hd6 :: [] ->
          concat " " ("NFoldLeft" :: (List.map (fun x -> (string_of_term x implicite)) (hd1 :: hd2 :: hd3 :: hd4 :: hd5 :: hd6 :: [])))
      | _ -> concat "" ("NFoldLeft " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | args1 :: (Obj o2) :: (Obj o3) :: (Obj o4) :: args5 :: args6 :: [] -> (

          let o2 = ((Obj.magic o2) :> mNTermObj) in
          let o3 = ((Obj.magic o3) :> mNTermObj) in
          let o4 = ((Obj.magic o4) :> mNTermObj) in
	  let start = o2#get_value in
	  let stop = o3#get_value in
	  let step = o4#get_value in
	    (* test if the sequence finishes *)
	    if (lt_big_int (mult_big_int (sub_big_int stop start) step) zero_big_int) then
	      (* no --> return the initial term *)
	      args6
	    else (
	    (* yes --> TODO *)

	      nfoldleft start stop step args5 args6 def

	    )
	      
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let nFoldLeftTerm =
  let o = new nFoldLeftTermObj in
    Obj o#my_self
;;

(* absolute *)

class mZAbsTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "ZAbs"
  method get_type = Forall ("H0", mZType, mNType)
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1 :: [] ->
          (string_of_term hd1 implicite)

      | _ -> concat "" ("ZAbs " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: [] -> (

          let o1 = ((Obj.magic o1) :> mZTermObj) in
            create_mNTerm (abs_big_int o1#get_value)
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mZAbsTerm =
  let o = new mZAbsTermObj in
    Obj o#my_self
;;

(* toString *)

class mNtoStringTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "NtoString"
  method get_type = Forall ("H0", mNType, stringType)
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1 :: [] ->
          (string_of_term hd1 implicite)

      | _ -> concat "" ("NtoString " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: [] -> (

          let o1 = ((Obj.magic o1) :> mZTermObj) in
            create_stringTerm (string_of_big_int o1#get_value)
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mNtoStringTerm =
  let o = new mNtoStringTermObj in
    Obj o#my_self
;;


let mN_init =

  add_def "StdLib.N.N" mNType Type TYPE ext_typechecker_state ext_typechecker_state;

  let o = new mNPlusTermObj in  
    add_def "StdLib.N.Nplus" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mNMinusNTermObj in  
    add_def "StdLib.N.Nminus" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mNMultiplyTermObj in  
    add_def "StdLib.N.Nmultiply" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mNDivideTermObj in  
    add_def "StdLib.N.Ndivide" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mNEqTermObj in  
    add_def "StdLib.N.Neq" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mNLtTermObj in  
    add_def "StdLib.N.Nlt" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mNLteTermObj in  
    add_def "StdLib.N.Nle" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mNGtTermObj in  
    add_def "StdLib.N.Ngt" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mNGteTermObj in  
    add_def "StdLib.N.Nge" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  add_coercion mN2ZTerm (Forall ("H0", mNType, mZType)) ext_typechecker_state ext_typechecker_state;

  let o = new nFoldLeftTermObj in  
    add_def "StdLib.N.NFoldLeft" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mZAbsTermObj in  
    add_def "StdLib.Z.ZAbs" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mNMinusZTermObj in  
    add_def "StdLib.N.NMinusZ" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mNtoStringTermObj in  
    add_def "StdLib.N.NtoString" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

;;
