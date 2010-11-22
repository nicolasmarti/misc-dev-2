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

open Set;;
open String;;

type var = string;;

module OrderedVar = 
    struct
      type t = var
      let compare x y = String.compare x y
    end;;

module VarSet = Set.Make(OrderedVar);; 

let vsin e s = not (VarSet.is_empty (VarSet.inter (VarSet.singleton e) s));;

let (+++) s1 s2 = VarSet.union s1 s2;;

let (++) elt s2 = VarSet.union (VarSet.singleton elt) s2;;

let list2varset l =

  List.fold_left (

    fun acc hd ->

      hd ++ acc

  ) VarSet.empty l
;;
