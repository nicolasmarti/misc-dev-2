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
open Printf;;
open Definition;;
open MN;;
open Big_int;;
open Mstring;;

(* The class for the type *)

class floatTypeObj =
object (self)
  inherit [term] pObj
  method get_name = "Float"
  method get_type = Type
  method pprint = (fun args _ -> self#get_name)
  method equal = (fun o -> (o#get_type = self#get_type && o#get_name = self#get_name))
  method my_self = (self :> term pObj)
  method exec = (fun args _ -> (Obj (self#my_self)))
  method show = (fun _ -> self#get_name)
end;;

let floatType = 
  let o = new floatTypeObj in
    Obj o#my_self
;;

(* The class for the term *)
class floatTermObj f =
object (self)
  inherit [term] pObj
  val mutable floatvalue = f
  method get_floatvalue = floatvalue
  method get_name = string_of_float floatvalue
  method get_type = floatType
  method equal = (fun o -> 
		    match (o#get_type, self#get_type) with
		      | (Obj ot, Obj mot) -> 
			  if (ot#equal mot) then
			    (((Obj.magic o) :> floatTermObj)#get_floatvalue = self#get_floatvalue)
			  else
			    false
		      | _ -> false		    
		 )
  method pprint = (fun args _ -> self#get_name)
  method my_self = (self :> term pObj)
  method exec = (fun args _ -> (Obj (self#my_self)))
  method show = (fun _ -> self#get_name)
end;;

let create_floatTerm f =
  let o = new floatTermObj f in
    Obj o#my_self
;;

(* Addition *)
class floatPlusTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "floatPlus"
  method get_type = Forall ("H0", floatType, Forall ("H0", floatType, floatType))
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " + " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("floatPlus " :: (string_of_listterm args implicite) :: [])
  )
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> floatTermObj) in
          let o2 = ((Obj.magic o2) :> floatTermObj) in
            create_floatTerm (o1#get_floatvalue +. o2#get_floatvalue)
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let floatPlusTerm =
  let o = new floatPlusTermObj in
    Obj o#my_self
;;

(* Substraction *)
class floatMinusTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "floatMinus"
  method get_type = Forall ("H0", floatType, Forall ("H0", floatType, floatType))
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " - " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("floatMinus " :: (string_of_listterm args implicite) :: [])
  )
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> floatTermObj) in
          let o2 = ((Obj.magic o2) :> floatTermObj) in
            create_floatTerm (o1#get_floatvalue -. o2#get_floatvalue)
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let floatMinusTerm =
  let o = new floatMinusTermObj in
    Obj o#my_self
;;

(* Multiplication *)
class floatMultiplyTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "floatMultiply"
  method get_type = Forall ("H0", floatType, Forall ("H0", floatType, floatType))
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " * " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("floatMultiply " :: (string_of_listterm args implicite) :: [])
  )
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> floatTermObj) in
          let o2 = ((Obj.magic o2) :> floatTermObj) in
            create_floatTerm (o1#get_floatvalue *. o2#get_floatvalue)
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let floatMultiplyTerm =
  let o = new floatMultiplyTermObj in
    Obj o#my_self
;;

(* Division *)
class floatDivideTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "floatDivide"
  method get_type = Forall ("H0", floatType, Forall ("H0", floatType, floatType))
  method pprint = (fun args implicite -> 
    match args with
      | hd1::hd2::[] ->
          concat "" ((string_of_term hd1 implicite) :: " / " :: (string_of_term hd2 implicite) :: [])

      | _ -> concat "" ("floatDivide " :: (string_of_listterm args implicite) :: [])
  )
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: (Obj o2) :: [] -> (

          let o1 = ((Obj.magic o1) :> floatTermObj) in
          let o2 = ((Obj.magic o2) :> floatTermObj) in
            create_floatTerm (o1#get_floatvalue /. o2#get_floatvalue)
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let floatDivideTerm =
  let o = new floatDivideTermObj in
    Obj o#my_self
;;

(* sqrt *)
class floatSqrtTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "floatSqrt"
  method get_type = Forall ("H0", floatType, floatType)
  method pprint = (fun args implicite -> 
    match args with
      | hd1::[] ->
          concat "" ("floatSqrt (" :: (string_of_term hd1 implicite) :: ")" :: [])

      | _ -> concat "" ("floatSqrt " :: (string_of_listterm args implicite) :: [])
  )
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: [] -> (

          let o1 = ((Obj.magic o1) :> floatTermObj) in
            create_floatTerm (sqrt o1#get_floatvalue)
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let floatSqrtTerm =
  let o = new floatSqrtTermObj in
    Obj o#my_self
;;

(* Conversion *)

class mN2FloatTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "N2Float"
  method get_type = Forall ("H0", mNType, floatType)
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1 :: [] ->
          concat "" ("N2Float " :: (string_of_term hd1 implicite) :: [])

      | _ -> concat "" ("N2Float " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: [] -> (

          let o1 = ((Obj.magic o1) :> mNTermObj) in
            create_floatTerm (float_of_big_int o1#get_value)
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mN2FloatTerm =
  let o = new mN2FloatTermObj in
    Obj o#my_self
;;

(* fold_left *)

let rec floatfoldleft start stop step f a def =
  if (start > stop) then
    a
  else
    let comp = (App (f, a :: (create_floatTerm start) :: [])) in
      floatfoldleft (start +. step) stop step f comp def

;;


class floatFoldLeftTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "FloatFoldLeft"
  method get_type = 
    let largs = ("A", Type) :: ("start", floatType) :: ("stop", floatType) :: ("step", floatType) :: ("f", Forall ("x", Var "A", Forall ("y", floatType, Var "A"))) :: ("a", Var "A") :: [] in
      largs_foralls (Var "A") largs      
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1 :: hd2 :: hd3 :: hd4 :: hd5 :: hd6 :: [] ->
          concat " " ("FloatFoldLeft" :: (List.map (fun x -> (string_of_term x implicite)) (hd1 :: hd2 :: hd3 :: hd4 :: hd5 :: hd6 :: [])))
      | _ -> concat "" ("FloatFoldLeft " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 

		   match args with
		     | args1 :: (Obj o2) :: (Obj o3) :: (Obj o4) :: args5 :: args6 :: [] -> (
			 
			 let o2 = ((Obj.magic o2) :> floatTermObj) in
			 let o3 = ((Obj.magic o3) :> floatTermObj) in
			 let o4 = ((Obj.magic o4) :> floatTermObj) in
			 let start = o2#get_floatvalue in
			 let stop = o3#get_floatvalue in
			 let step = o4#get_floatvalue in
			   (* test if the sequence finishes *)
			   if ((stop -. start) *. step < 0.0) then
			     (* no --> return the initial term *)
			     args6
			   else (
			     (* yes --> TODO *)
			     let res = floatfoldleft start stop step args5 args6 def in
			       res

			   )
			     
		       )       
		     | a -> App (Obj self#my_self, a)


		)
  method show = (fun _ -> self#get_name)
end;;

let floatFoldLeftTerm =
  let o = new floatFoldLeftTermObj in
    Obj o#my_self
;;

(* toString *)

class mFloattoStringTermObj  =
object (self)
  inherit [term] pObj
  method get_name = "FloattoString"
  method get_type = Forall ("H0", floatType, stringType)
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method pprint = (fun args implicite -> 
    match args with
      | hd1 :: [] ->
          (string_of_term hd1 implicite)

      | _ -> concat "" ("FloattoString " :: (string_of_listterm args implicite) :: [])
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | (Obj o1) :: [] -> (

          let o1 = ((Obj.magic o1) :> floatTermObj) in
            create_stringTerm (string_of_float o1#get_floatvalue)
        )       
      | a -> App (Obj self#my_self, a)


  )
  method show = (fun _ -> self#get_name)
end;;

let mFloattoStringTerm =
  let o = new mFloattoStringTermObj in
    Obj o#my_self
;;


let mfloat_init =

  add_def "StdLib.float.Float" floatType Type TYPE ext_typechecker_state ext_typechecker_state;

  let o = new floatPlusTermObj in  
    add_def "StdLib.float.Floatplus" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new floatMinusTermObj in  
    add_def "StdLib.float.Floatminus" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new floatMultiplyTermObj in  
    add_def "StdLib.float.Floatmultiply" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new floatDivideTermObj in  
    add_def "StdLib.float.Floatdivide" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;
  
  let o = new floatSqrtTermObj in  
    add_def "StdLib.float.FloatSqrt" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  add_coercion mN2FloatTerm (Forall ("H0", mNType, floatType)) ext_typechecker_state ext_typechecker_state;

  let o = new floatFoldLeftTermObj in  
    add_def "StdLib.float.FloatFoldLeft" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;
    
  let o = new mFloattoStringTermObj in
    add_def "StdLib.float.FloatToString" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

;;
