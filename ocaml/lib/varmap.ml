(*
 This file is part of Mymms.

 Mymms is free software: you can redistribute it and/or modify
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

open Map;;
open String;;
open Varset;;

module VarMap = Map.Make(OrderedVar);; 

let vmdomain vm =

  VarMap.fold (fun k y x -> k ++ x) vm VarSet.empty

;;

let vmext vm =

  VarMap.fold (fun k y x -> (k, y) :: x) vm []

;;

let find_in_varmap vm x =
  
  try
    
    Some (VarMap.find x vm)

  with

    | _ -> None
;;

let varmap_union vm1 vm2 =

  VarMap.fold (

    fun key data acc ->

      VarMap.add key data acc


  ) vm2 vm1 
;;

let varmap_diff vm1 vm2 =
  
  VarSet.fold (

    fun hd acc ->
      
      VarMap.remove hd acc

  ) (vmdomain vm2) vm1  

;;

let varmap_filter m f =
  VarMap.fold (

    fun k v acc ->

      if (f k v) then
	VarMap.add k v acc
      else
	acc

  ) m VarMap.empty
;;

let varmap_vallist m =
  List.map (fun x -> snd x) (vmext m)
;;
