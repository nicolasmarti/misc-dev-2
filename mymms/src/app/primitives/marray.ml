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
open Array;;
open Big_int;;
open Termeq;;
open Printf;;
open Extstate;;
open Definition;;

(* The class for the type *)

class mArrayTypeObj =
object (self)
  inherit [term] pObj
  method get_name = "Array"
  method get_type = Forall ("A", Type, Forall ("n", mNType, Type))
  method pprint = (fun args implicite -> 
		     String.concat "" (self#get_name :: (string_of_listterm2 args implicite) :: [])
		  )
  method equal = (fun o -> (o#get_type = self#get_type && o#get_name = self#get_name))
  method my_self = (self :> term pObj)
  method exec = (fun args _ -> (App (Obj (self#my_self), args)))
  method show = (fun _ -> self#get_name)
end;;

let mArrayType = 
  let o = new mArrayTypeObj in
    Obj o#my_self
;;

(* The class for the term *)
class mArrayObj t n a =
object (self)
  inherit [term] pObj
  val mutable arrayvalue : term array = a
  val mutable typevalue : term = t
  val mutable sizevalue : int = n
  method get_arrayvalue = arrayvalue
  method get_typevalue = typevalue
  method get_sizevalue = sizevalue
  method get_name = String.concat "" ("{0x" :: (string_of_int (((Obj.magic self) :> int))) :: "}" :: [])
  method get_type = App(mArrayType, (self#get_typevalue)::(create_mNTerm (big_int_of_int (self#get_sizevalue)))::[])
  method pprint = (fun args _ -> self#get_name)
  method my_self = (self :> term pObj)
  method exec = (fun args _ -> (App (Obj (self#my_self), args)))
  method show = (fun implicite -> 		   
		   self#get_name
		)  
  method equal = (fun o -> false)
end;;

let create_mArray t n a =
  let o = new mArrayObj t n a in
    Obj o#my_self
;;


(* Construction *)
class mArrayMakeObj = 
object (self)
  inherit [term] pObj
  method get_name = "make"
  method get_type = Forall ("A", Type, Forall ("a", Var "A", Forall ("n", mNType, App (mArrayType, (Var "A") :: (Var "n") :: []))))
  method pprint = (fun args implicite -> 
		     String.concat "" (self#get_name :: (string_of_listterm2 args implicite) :: [])
		  )
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
    
    match args with
      | hd1 :: hd2 :: (Obj o) :: [] -> (

          let o = ((Obj.magic o) :> mNTermObj) in
	  let n = int_of_big_int o#get_value in
	  let a = Array.make n hd2 in
	    (create_mArray hd1 n a)	    
            
        )       
      | a -> App (Obj self#my_self, a)
	  

  )
  method show = (fun _ -> self#get_name)
end;;

let mArrayMakeTerm =
  let o = new mArrayMakeObj in
    Obj o#my_self
;;


(* lookup *)
class mArrayGetObj = 
object (self)
  inherit [term] pObj
  method get_name = "get"
  method get_type = Forall ("A", Type, Forall ("n", mNType, Forall ("a",  App (mArrayType, (Var "A") :: (Var "n") :: []), Forall ("i", mNType, Var "A"))))
  method pprint = (fun args implicite -> 
		     String.concat " " (self#get_name :: (List.map (fun x -> string_of_term x implicite) args))
		  )
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
		   match args with
		     | ty :: (Obj n) :: (Obj a) :: (Obj i) :: [] -> (
			 let a = ((Obj.magic a) :> mArrayObj) in
			 let i = ((Obj.magic i) :> mNTermObj) in
			 let i = int_of_big_int i#get_value in
			   try (
			     
			     let v = Array.get a#get_arrayvalue i in
			       v
				 
			   ) with 
			     | Invalid_argument _ -> printf "Error: get vector out of bound\n\n"; App (Obj self#my_self, args)
				 
		       )       
		     | a -> App (Obj self#my_self, a)
			 
			 
		)
  method show = (fun _ -> self#get_name)
end;;

let mArrayGetTerm =
  let o = new mArrayGetObj in
    Obj o#my_self
;;

(* Mutation (with copy) *)
class mArraySetObj = 
object (self)
  inherit [term] pObj
  method get_name = "set"
  method get_type = Forall ("A", Type, Forall ("n", mNType, Forall ("a",  App (mArrayType, (Var "A") :: (Var "n") :: []), Forall ("i", mNType, Forall ("e", Var "A", App (mArrayType, (Var "A") :: (Var "n") :: []))))))
  method pprint = (fun args implicite -> 
		     String.concat " " (self#get_name :: (List.map (fun x -> string_of_term x implicite) args))
		  )
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
		   match args with
		     | ty :: (Obj n) :: (Obj a) :: (Obj i) :: e :: [] -> (
			 let a = ((Obj.magic a) :> mArrayObj) in
			 let i = ((Obj.magic i) :> mNTermObj) in
			 let i = int_of_big_int i#get_value in
			 let a' = Array.copy a#get_arrayvalue in
			   try (
			     
			     Array.set a' i e;
			     create_mArray a#get_typevalue a#get_sizevalue a'
				 
			   ) with 
			     | Invalid_argument _ -> printf "Error: set vector out of bound\n\n"; App (Obj self#my_self, args)
				 
		       )       
		     | a -> App (Obj self#my_self, a)
			 
			 
		)
  method show = (fun _ -> self#get_name)
end;;

let mArraySetTerm =
  let o = new mArraySetObj in
    Obj o#my_self
;;

(* Append *)
class mArrayAppendObj = 
object (self)
  inherit [term] pObj
  method get_name = "append"
  method get_type = Forall ("A", Type, Forall ("n1", mNType, Forall ("a1",  App (mArrayType, (Var "A") :: (Var "n1") :: []), Forall ("n2", mNType, Forall ("a2",  App (mArrayType, (Var "A") :: (Var "n2") :: []), App (mArrayType, (Var "A") :: (App (mNPlusTerm, (Var "n1") :: (Var "n2") :: [])) :: []))))))
  method pprint = (fun args implicite -> 
		     String.concat " " (self#get_name :: (List.map (fun x -> string_of_term x implicite) args))
		  )
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
		   match args with
		     | ty :: (Obj n1) :: (Obj a1) :: (Obj n2) :: (Obj a2) :: [] -> (
			 let a1 = ((Obj.magic a1) :> mArrayObj) in
			 let a2 = ((Obj.magic a2) :> mArrayObj) in
			 let n1 = ((Obj.magic n1) :> mNTermObj) in
			 let n1 = int_of_big_int n1#get_value in
			 let n2 = ((Obj.magic n2) :> mNTermObj) in
			 let n2 = int_of_big_int n2#get_value in
			   create_mArray a1#get_typevalue (n1+n2) (Array.append a1#get_arrayvalue a2#get_arrayvalue)
			     
		       )       
		     | a -> App (Obj self#my_self, a)
			 
			 
		)
  method show = (fun _ -> self#get_name)
end;;

let mArrayAppendTerm =
  let o = new mArrayAppendObj in
    Obj o#my_self
;;

(* SubArray *)
class mArraySubObj = 
object (self)
  inherit [term] pObj
  method get_name = "append"
  method get_type = Forall ("A", Type, Forall ("n", mNType, Forall ("a",  App (mArrayType, (Var "A") :: (Var "n") :: []),  Forall ("start", mNType,  Forall ("length", mNType, App (mArrayType, (Var "A") :: (Var "length") :: []))))))
  method pprint = (fun args implicite -> 
		     String.concat " " (self#get_name :: (List.map (fun x -> string_of_term x implicite) args))
		  )
  method equal = (
    fun o ->
      (term_eq self#get_type o#get_type (DefNode VarMap.empty)) && (self#get_name = o#get_name)
  )
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 
		   match args with
		     | ty :: (Obj n1) :: (Obj a1) :: (Obj start) :: (Obj len) :: [] -> (
			 let a1 = ((Obj.magic a1) :> mArrayObj) in
			 let start = ((Obj.magic start) :> mNTermObj) in
			 let start = int_of_big_int start#get_value in
			 let len = ((Obj.magic len) :> mNTermObj) in
			 let len = int_of_big_int len#get_value in
			   try (
			     
			     create_mArray ty len (Array.sub a1#get_arrayvalue start len)
				 
			   ) with 
			     | Invalid_argument _ -> printf "Error: sub array out of bound\n\n"; App (Obj self#my_self, args)

			     
		       )       
		     | a -> App (Obj self#my_self, a)
			 
			 
		)
  method show = (fun _ -> self#get_name)
end;;

let mArraySubTerm =
  let o = new mArraySubObj in
    Obj o#my_self
;;


let marray_init =

  let o = new mArrayTypeObj in
  add_def "StdLib.Array.Array" (Obj (o#my_self)) (o#get_type) TYPE ext_typechecker_state ext_typechecker_state;
  
  let o = new mArrayMakeObj in
    add_def "StdLib.Array.make" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mArrayGetObj in
    add_def "StdLib.Array.get" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mArraySetObj in
    add_def "StdLib.Array.set" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mArrayAppendObj in
    add_def "StdLib.Array.append" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

  let o = new mArraySubObj in
    add_def "StdLib.Array.sub" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;


;;

