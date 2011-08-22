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
open Interp;;

open Vm;;

open List;;
open Listext;;
open Kernel;;

open Term;;

open Output;;

(* The class for the type *)

class vmTermObj te ty (m: block1 VarMap.t) (c: block1) (l: int) =
object (self)
  inherit [term] pObj
  method get_name = "vmTerm"
  method get_term = te
  method get_type = ty
  method get_blocks = m
  method get_main = c
  method get_level = l
  method pprint = (fun args _ -> self#get_name)
  method equal = (fun o -> (o#get_type = self#get_type && o#get_name = self#get_name))
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 

		   (*printf "exec\n\n"; flush stdout;*)
		   let (l, _) = decomp_foralls self#get_type in

		   if (length args == length l) then ( 

		     try (
		       let (cargs, margs, largs) =
			 List.fold_left (
			   
			   fun acc hd ->
			     
			     let (c, m , l) = acc in
			     let (c' , m' , l') = translate_lambda2cmd1 "args" l hd m def in
			       (c @ c', m', l')
				 
			 ) ([], self#get_blocks, self#get_level) (rev (List.map (fun te -> term2iterm te [] def) args)) in
			 
		       let c = cargs @ self#get_main @ (list_of_n_elt Apply1 (List.length args)) in
		       let m = margs in
		       let c = c @ Return1::[] in
		       let b = concat_block1_2 c m in
			 (*printf "concat block\n\n"; flush stdout;*)
		       let m = build_label_offset b 0 in
			 (*printf "build label offset\n\n"; flush stdout;*)
		       let c = Array.of_list (translate_block1_to_block2 b m) in
			 (*printf "translate block1 -> block2\n\n"; flush stdout;*)
		       let res = vm_exec2 c 0 [] [] state.tpck.def in
		       let it = data22iterm res in
		       let t = iterm2term it 0 [] [] in
			 
			 (*printf "t := %s\n\n" (string_of_term t VarMap.empty); flush stdout;*)
			 
			 match check_term (List.hd State.state.path) t (Some ty) state.tpck.def state.tpck.coercion (oracleslist state.tpck.oracles) state.tpck.overload state.tpck.implicite with
			   | None -> App (Obj self#my_self, args)
			   | Some (te, ty) ->
			       te			       
		     ) with
		       | Translationterm2iterm s -> print_error (sprintf "%s\n" s); App (Obj self#my_self, args)
		       | Translationiterm2cmd1 s -> print_error (sprintf "%s\n" s); App (Obj self#my_self, args)
		       | Translationdata22iterm s -> print_error (sprintf "%s\n" s); App (Obj self#my_self, args)
		       | VMExec s -> print_error (sprintf "%s\n" s); App (Obj self#my_self, args)
		       | Failure s -> print_error (sprintf "%s\n" s); App (Obj self#my_self, args)
		       | Not_found -> print_error "not found\n"; App (Obj self#my_self, args)
		   ) else
		     App (Obj self#my_self, args)
 
		     



		)
  method show = (fun _ -> String.concat "" ("|" :: (string_of_term self#get_term VarMap.empty) :: "|" :: [] ))
end;;

let vmTerm ty te = 
  let it = term2iterm te [] state.tpck.def in
  let (c, m, l) = translate_lambda2cmd1  "main" 0 it (VarMap.empty) state.tpck.def in    
  let o = new vmTermObj te ty m c l in
    Obj o#my_self
;;

(* The class for the type *)

class buildVmTermObj =
object (self)
  inherit [term] pObj
  method get_name = "buildVmTerm"
  method get_type = Forall ("A", Type, Forall ("a", Var "A", Var "A"))
  method pprint = (fun args _ -> self#get_name)
  method equal = (fun o -> (o#get_type = self#get_type && o#get_name = self#get_name))
  method my_self = (self :> term pObj)
  method exec = (fun args def -> 

		   (*printf "args := %s\n\n" (string_of_listterm args VarMap.empty); flush stdout;*)

		   match args with
		     | t1 :: t2 :: [] -> (

			 (*printf "yes!\n\n"; flush stdout;*)
			vmTerm t1 t2 

		       )       
		     | a -> 
			 (*printf "no!\n\n"; flush stdout;*)
			 App (Obj self#my_self, a)
			 
		)
  method show = (fun _ -> self#get_name)
end;;

let buildVmTerm = 
  let o = new buildVmTermObj in
    Obj o#my_self
;;


let mvm_init =

  let o = new buildVmTermObj in  
    add_def "StdLib.VM.vmbuild" (Obj (o#my_self)) (o#get_type) FUNCTION ext_typechecker_state ext_typechecker_state;

;;
