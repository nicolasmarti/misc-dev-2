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

open Printf;;
open List;;
open String;;
open Varset;;
open Freshness;;
open Def;;
open Term;;
open Rewrite;;
open Printer;;
open Varmap;;
open Definition;;


let rec unfold_cste c def =
  match finddef c def with
    | None -> Cste c
    | Some (n , (te, ty, nature)) -> te
;;


(*

  unfold:
  
  - is use to unfold type in typechecking (that is already have been typed to type)
  - use beta reduction

*)

let rec unfold_term te def =
  (*
  printf "unfold_term: ";
  print_term te VarMap.empty;
  printf "\n\n";
  *)
  app_nf (
    match te with
      | Avar -> Avar
      | Obj o -> Obj o
      | Cste v -> (
	  unfold_cste v def
        )
      | App (t1, t2) -> (
          match (unfold_term t1 def) with
            | Lambda (x, t11, t12) -> 
                (App (Lambda (x, t11, t12), t2))
            | Cste v ->
                if (unfold_term t1 def = t1) then
                  te
                else
                  (App ((unfold_term t1 def), t2))
            | _ -> App (unfold_term t1 def, unfold_listterm t2 def)
        )
      | Match (te', lde, ty, ind) ->
          let te1 = (Match (unfold_term te' def, unfold_listterm lde def, 
                            (match ty with
                               | None -> None
                               | Some ty -> Some (unfold_term ty def)
			    ),
                            (match ind with
                               | None -> None
                               | Some ind -> Some (unfold_term ind def)
			    )
			   )
		    ) in
            te1
      | AdvMatch (t, ldes, ty) ->
	  let t = unfold_term t def in
	  let ty = 
	    match ty with
	      | None -> None
	      | Some ty -> Some (unfold_term ty def)
	  in
	  let ldes = unfold_listtermterm ldes def in
	    AdvMatch (t, ldes, ty)      
	  
      (* pas bien !! 
	 Pourquoi ????
	 | Ind (x, la, ty, lc) ->
	 Ind (x, unfold_listvarterm la def, unfold_term ty def, unfold_listterm lc def)
	 | Forall (x, t1, t2) ->
	 Forall (x, unfold_term t1 def, unfold_term t2 def)
	 
	 | Lambda, let ????
      *)
      | _ -> te
  )
and unfold_listterm lt def =
  match lt with
    | [] ->[]
    | hd :: tl ->
        (unfold_term hd def) :: (unfold_listterm tl def)
and unfold_listvarterm lt def =
  match lt with
    | [] ->[]
    | (hd1, hd2) :: tl ->
        (hd1, (unfold_term hd2 def)) :: (unfold_listvarterm tl def)
and unfold_listtermterm lt def =
  match lt with
    | [] ->[]
    | (hd1, hd2) :: tl ->
	(unfold_term hd1 def, unfold_term hd2 def) :: (unfold_listtermterm tl def)
;;

        
let rec unfold_term_fp te def =
  let te' = unfold_term te def in
    if (te' = te) then 
      te
    else 
      unfold_term_fp te' def
;;

let unfold_listterm_fp lt def =
  List.map (

    fun hd ->

      unfold_term_fp hd def

  ) lt
;;



