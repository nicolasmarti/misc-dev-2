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

open Def;;
open Printer;;
open Freshness;;
open Term;;

let rec cons_comcl_val lc x =
  match lc with
    | [] -> true
    | hd :: tl ->
        let (_, ccl) = decomp_foralls hd in
        let (fct, _) = decomp_app ccl in
          if (fct = Var x) then
            cons_comcl_val tl x
          else false
;;

        

let rec indwf t =
  match t with
    | Type -> true
    | Obj o -> true
    | Cste n -> true
    | Var v -> true
    | Let (s, t1, t2) -> indwf t1 && indwf t2
    | Lambda (s, t1, t2) -> indwf t1 && indwf t2
    | Forall (s, t1, t2) -> indwf t1 && indwf t2
    | Phi (s, t1, t2, l, t4) -> listvarterm_indwf t1 && indwf t2 && indwf t4
    | Ind (s, t1, t2, t3) -> cons_comcl_val t3 s
    | App (t1, t2) -> indwf t1 && listterm_indwf t2
    | Match (t1, l, t2, ind) -> indwf t1 && listterm_indwf l && (
        match t2 with
          | None -> true
          | Some t2 ->
              indwf t2
      ) && (
        match ind with
          | None -> true
          | Some ind ->
              indwf ind
      )
    | Cons (n, t1) -> indwf t1
    | AdvMatch _ -> false
    | Avar -> false
and listterm_indwf lt =
  match lt with
    | [] -> true
    | hd :: tl ->
        (indwf hd) && (listterm_indwf tl)
and listvarterm_indwf ctxt =
  match ctxt with
    | [] -> true
    | (hd1, hd2) :: tl ->
        (indwf hd2) && (listvarterm_indwf tl);;

