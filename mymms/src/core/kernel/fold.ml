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
open Alpha;;
open Beta;;
open Printer;;
open Termeq;;
open Listext;;
open Unfold;;
open Varmap;;
open Definition;;

let rec fold_atom' te l bv def =  
match l with
    | [] -> te
    | (hd1, hd2) :: tl ->
        (*printf "( %s, " hd1; print_term hd2 VarMap.empty; printf ") in \n%s\n" (string_of_term te VarMap.empty); flush stdout;*)
        fold_atom' (rewrite_term_term_term te hd2 (Cste hd1) bv def) tl bv def
;;

let fold_atom te bv (def: definition) =
  fold_atom' 
    te 
    (List.fold_left (fun a x -> let (n, (te, ty, nature)) = x in (n,te)::a) [] (definition2ext [] def))
    bv
    def
;;

(* there may be problems:

   - assure that the def are closed term !
   - do we have to take care about bounded variable for fold_atom ??
*)

let rec fold_term te bv def =
  (*printf "fold_term: "; print_term te VarMap.empty; printf "\n"; flush stdout;
  let te' =*)
  let te' = fold_atom te bv def in
    if (te = te') then (
      match te with
        | Let (x, t1, t2) ->
            Let (x, (fold_term t1 bv def), (fold_term t2 (x ++ bv) def))
        | Lambda (x, t1, t2) ->
            Lambda (x, (fold_term t1 bv def), (fold_term t2 (x ++ bv) def))
        | Forall (x, t1, t2) ->
            Forall (x, (fold_term t1 bv def), (fold_term t2 (x ++ bv) def))
        | Phi (x, la, ty, lda, ld) ->
            Phi (x, (fold_args la bv def), (fold_term ty ((list2varset (list_proj1 la)) +++ bv) def), lda, (fold_term ld (x ++ ((list2varset (list_proj1 la)) +++ bv)) def))
        | Ind (x, la, ty, lc) ->
            Ind (x, (fold_args la bv def), (fold_term ty ((list2varset (list_proj1 la)) +++ bv) def), (fold_listterm lc (x ++ ((list2varset (list_proj1 la)) +++ bv)) def))
        | Match (te, ld, ty, ind) ->
            Match ((fold_term te bv def), (fold_listterm ld bv def), 
		   (match ty with
                     | None -> None
                     | Some ty -> Some (fold_term ty bv def)
		   ),
		   (match ind with
                     | None -> None
                     | Some ind -> Some (fold_term ind bv def)
		   )
            )
        | App (t1, t2) ->
            App ((fold_term t1 bv def), (fold_listterm t2 bv def))
        | Cons (n, t1) ->
            Cons (n, (fold_term t1 bv def))
        | _ -> te
    ) else
      te'
  (*in
  printf "fold_term res : "; print_term te' VarMap.empty; printf "\n"; flush stdout;
	te'*)
    
and fold_listterm lte bv def =
  match lte with
    | [] -> []
    | hd :: tl ->
        (fold_term hd bv def) :: (fold_listterm tl bv def)
and fold_args la bv def =
  match la with
    | [] -> []
    | (hd1, hd2) :: tl ->
        (hd1, (fold_term hd2 bv def)) :: (fold_args tl (hd1 ++ bv) def)      
;;

let rec fold te bv def =
  (*printf "fold: "; print_term te VarMap.empty ; printf "\n"; flush stdout;
  let te'=*)
    let te' = fold_term te bv def in
      if (te = te') then
	te
      else
	(
          fold te' bv def
	)
(*in 
  printf "fold res : "; print_term te' VarMap.empty; printf "\n"; flush stdout;
	  te'*)
    
;;

let rec fold_ctxt c bv def =
  match c with
    | [] -> []
    | (hd1, hd2) :: tl ->
        (hd1, fold hd2 bv def) :: (fold_ctxt tl bv def)
;;


