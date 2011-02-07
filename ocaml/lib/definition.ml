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

  Copyright (C) Nicolas Marti
*)

open List;;
open String;;
open Varset;;
open Varmap;;
open String;;

type 'a definition = 
  | DefNode of ('a definition) VarMap.t
  | DefLeaf of 'a VarMap.t
;;


let rec defname2path (name: string) =  
  try
    let i = String.index_from name 0 '.' in
      (String.sub name 0 i)::(defname2path (String.sub name (i+1) (String.length name - i - 1)))

  with
    | _ -> name::[]
;;

let rec findpath (path: string list) d =
  match path with
    | [] -> None
    | x::[] -> (
	match d with
	  | DefNode _ -> None
	  | DefLeaf d ->
	      try (
		let res = VarMap.find x d in
		  Some res
	      ) with
		| _ -> None
      )
    | x::xs::tl -> (
	match d with
	  | DefNode d -> (
	      try (
		let d' = VarMap.find x d in
		  findpath (xs::tl) d'
	      ) with
		| _ -> None
	    )
	  | DefLeaf _ ->
	      None
      )
;;

let rec finddef (name: string) d = 
  match findpath (defname2path name) d with
    | None -> (
	
	match d with
	  | DefLeaf _ -> None
	  | DefNode d ->
	      (* fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b *)
	      VarMap.fold (
		
		fun k v acc ->
		  match acc with
		    | Some _ -> acc
		    | None ->
			
			match finddef name v with
			  | None -> None
			  | Some (n, res) ->
			      Some (
				concat "." (k :: n ::[]),
				res
			      )


	      ) d None

      )
    | Some res -> Some (name, res)
;;

let rec insertpathdef (name: string list) elt d = 
  match name with
    | [] -> None
    | x::[] -> (
	
	match d with
	  | DefNode _ -> None
	  | DefLeaf d -> 
	      try 
		let _ = VarMap.find x d in
		  None
	      with
		| _ -> Some (DefLeaf (VarMap.add x elt d))
	
      )
    | x::xs::tl ->

	match d with
	  | DefLeaf _ -> None
	  | DefNode d -> 
	      try (
		let d' = VarMap.find x d in
		  match insertpathdef (xs::tl) elt d' with
		    | None -> None
		    | Some d'' ->
			Some (DefNode (VarMap.add x d'' d))
		  
	      ) with
		| _ -> 
		    match tl with
		      | [] -> (
			  match insertpathdef (xs::tl) elt (DefLeaf (VarMap.empty)) with
			    | None -> None
			    | Some d' ->
				Some (DefNode (VarMap.add x d' d))
			)
		      | _ -> (
			  match insertpathdef (xs::tl) elt (DefNode (VarMap.empty)) with
			    | None -> None
			    | Some d' ->
				Some (DefNode (VarMap.add x d' d))
			)
;;

let insertdef (name: string) elt d = 
  insertpathdef (defname2path name) elt d
;;

(* TODO merge 2 definitions *)
let rec mergedef d1 d2 =
  match (d1, d2) with
    | (DefNode d1, DefNode d2) -> (

	let dom1 = vmdomain d1 in
	let dom2 = vmdomain d2 in
	let dom12 = VarSet.inter dom1 dom2 in
	let dom1 = VarSet.diff dom1 dom12 in
	let dom2 = VarSet.diff dom2 dom12 in
	let dom12merge =
	  List.fold_left (
	    fun acc hd ->
	      let d1' = VarMap.find hd d1 in
	      let d2' = VarMap.find hd d2 in
		match (acc, mergedef d1' d2') with
		  | (Some m, Some d) ->
		      Some (VarMap.add hd d m)
		  | _ -> None	

	  ) (Some VarMap.empty) (VarSet.elements dom12) in
	  match dom12merge with
	    | None -> None
	    | Some m ->
		Some (
		  DefNode (
		    varmap_union
		      (
			varmap_union
			  (varmap_filter
			     d1
			     (fun n v -> 
				List.fold_left 
				  (
				    fun acc hd ->
				      acc || (hd = n)
				  ) false (VarSet.elements dom1)
			     )
			  )
			  (varmap_filter d2
			     (fun n v -> 
				List.fold_left 
				  (
				    fun acc hd ->
				      acc || (hd = n)
				  ) false (VarSet.elements dom2)
			     )
			  )
		      )
		      m
		  )
		)
      )
    | (DefLeaf d1, DefLeaf d2) -> (
	let dom1 = vmdomain d1 in
	let dom2 = vmdomain d2 in
	let dom12 = VarSet.inter dom1 dom2 in
	  if (not (VarSet.is_empty dom12)) then None else
	    Some (DefLeaf (varmap_union d1 d2))
      )

    | _ -> None
;;

let rec definition2nameset d =
  match d with
    | DefNode v -> (
	
	VarMap.fold (

	  fun k v acc ->
	    (* pourquoi + k ??? *)
	    (*k ++ (acc +++ (definition2nameset v))*)
	    (acc +++ (definition2nameset v))

	) v VarSet.empty
	
      )
	
    | DefLeaf m -> (

	(* fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b *)
	vmdomain m
	

      )
;;
	
let rec definition2ext (name: string list) d =
  
  match d with
    | DefNode v -> (

	VarMap.fold (

	  fun k v acc ->

	    (definition2ext ((concat "." (name @ k :: []))::[]) v) @ acc


	) v []

      )

    | DefLeaf m -> (

	(* fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b *)
	VarMap.fold (

	  fun k v acc ->

	      (concat "." (name @ k :: []), v) :: acc

	) m []
	

      )
	
;;

let definitiondomain d =
  let l = definition2ext [] d in
    List.fold_left (

      fun acc hd ->
	let (n, _) = hd in
	  n ++ acc

    ) VarSet.empty l

;;

let rec mkdefinitionfromdef (path: string) def =
  try
    let i = String.index_from path 0 '.' in
    let subdef = (mkdefinitionfromdef (String.sub path (i+1) (String.length path - i - 1)) def) in
      DefNode (VarMap.add (String.sub path 0 i) subdef VarMap.empty)

  with
    | _ -> 
	DefNode (VarMap.add path (DefLeaf def) VarMap.empty)
;;


let rec diffdef d1 d2 =
  match (d1, d2) with
    | (DefNode d1, DefNode d2) -> (

	let dom1 = vmdomain d1 in
	let dom2 = vmdomain d2 in
	let dom12 = VarSet.inter dom1 dom2 in
	let dom1 = VarSet.diff dom1 dom12 in
	let dom12merge =
	  List.fold_left (
	    fun acc hd ->
	      let d1' = VarMap.find hd d1 in
	      let d2' = VarMap.find hd d2 in
		match (acc, diffdef d1' d2') with
		  | (Some m, Some d) ->
		      Some (VarMap.add hd d m)
		  | _ -> None	

	  ) (Some VarMap.empty) (VarSet.elements dom12) in
	  match dom12merge with
	    | None -> None
	    | Some m ->
		Some (
		  DefNode (
		    varmap_union
		      (
			(varmap_filter
			   d1
			   (fun n v -> 
			      List.fold_left 
				(
				  fun acc hd ->
				    acc || (hd = n)
				) false (VarSet.elements dom1)
			   )
			)
		      )
		      m
		  )
		)
      )
	

    | (DefLeaf d1, DefLeaf d2) -> (

	let nd = varmap_diff d1 d2 in
	  Some (DefLeaf nd)

      )
    | _ -> None
;;

let rec getsubdefpath (path: string list) d =
  match path with
    | [] -> Some d
    | hd::tl ->
	match d with
	  | DefLeaf _ -> None
	  | DefNode d ->
	      try (
		let d = VarMap.find hd d in
		  getsubdefpath tl d
	      ) with
		| _ -> None

;;

let getsubdef (name: string) d = 
  getsubdefpath (defname2path name) d
;;
