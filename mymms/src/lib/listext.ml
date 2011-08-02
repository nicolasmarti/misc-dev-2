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

open List;;

  

let rec nth_head n l =
  match n with
    | 0 -> []
    | j ->
        match l with
          | [] -> []
          | hd :: tl ->
              hd :: (nth_head (j-1) tl)
;;

let rec nth_tail n l =
  match n with
    | 0 -> l
    | j ->
        match l with
          | [] -> []
          | hd :: tl ->
              nth_tail (j-1) tl
;;

let list_insert l n e =
  (nth_head n l) @ e :: (nth_tail n l)
;;

let rec remove_indices' l ind ci =
  match ind with
    | [] -> l
    | hdi :: tli ->
        if (hdi = ci) then (
          match l with
            | [] -> []
            | hd :: tl -> remove_indices' tl tli (ci+1)
        ) else (
          match l with
            | [] -> []
            | hd :: tl -> hd :: remove_indices' tl ind (ci+1)
        )
;;

let remove_indices l ind = 
  remove_indices' l ind 0
;;

let rec list_proj1 l =
  match l with
    | [] -> []
    | (hd1, hd2) :: tl ->
        hd1 :: (list_proj1 tl)
;;

let rec list_proj2 l =
  match l with
    | [] -> []
    | (hd1, hd2) :: tl ->
        hd2 :: (list_proj2 tl)
;;

let rec find_list l n =
  match l with 
    | [] -> None
    | (hd1, hd2) :: tl ->
        if (hd1 = n) then 
          Some (hd2)
        else
          find_list tl n
;;

let rec list_of_n_elt e n =
  match n with
    | 0 -> []
    | n -> (e :: (list_of_n_elt e (n - 1)))
;;

let rec list2listoption l =
  match l with
    | [] -> []
    | hd :: tl ->
        (Some hd) :: (list2listoption tl)
;;

let rec list_last l =
  match l with
    | [] -> None
    | hd :: [] -> Some hd
    | hd :: tl ->
	list_last tl
;;

let rec list_remove e l =
  match l with
    | [] -> []
    | hd :: tl ->
	if (hd = e)
	then 
	  list_remove e tl
	else
	  hd ::(list_remove e tl)
;;

let rec list_remove_fst e l =
  match l with
    | [] -> []
    | (hd1, hd2) :: tl ->
	if (hd1 = e)
	then 
	  list_remove_fst e tl
	else
	  (hd1, hd2) ::(list_remove_fst e tl)
;;

let rec list_index x l n =
 match l with
   | [] -> raise (Failure "list_index")
   | hd::tl -> 
       if (x = hd) then n
       else
	 list_index x tl (n+1)
;;

let rec last l =
  match l with
    | [] -> raise (Failure "last")
    | hd :: [] -> hd
    | hd :: tl -> last tl
;;

let rec init l =
  match l with
    | [] -> raise (Failure "init")
    | hd :: [] -> []
    | hd :: tl -> hd :: (init tl)
;;

let rec list_insert' i l1 li e =
  match li with
    | [] -> l1
    | hd :: tl ->
	if (i = hd) then
	  e :: (list_insert' (i+1) l1 tl e)
	else
	  (
	    match l1 with 
		(* to be correct should test the emptyness of li ... *)
	      | [] -> []
	      | hd :: tl ->
		  hd :: (list_insert' (i+1) tl li e)

	  )
;;
	  
let list_insert l li e =
  list_insert' 0 l li e
;;

let rec concatenate e l =
  match l with
    | [] -> []
    | hd :: tl ->
	match tl with
	  | [] -> hd
	  | _ -> hd @ e :: (concatenate e tl)
;;
	

let rec iota s e = 
  if (s = e) then e::[] else
    s :: (iota (s+1) e)
;;

let rec fold_left2 f acc l =
  match l with
    | [] -> acc
    | hd::tl ->
	let (acc', l') = f acc hd tl in
	  fold_left2 f acc' l'
;;

let rec intercalate e l =
  match l with
    | [] -> []
    | hd::[] -> hd::[]
    | hd :: tl -> hd :: e :: (intercalate e tl)
;;
