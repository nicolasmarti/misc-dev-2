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
open Varmap;;
open Freshness;;
open Def;;
open Term;;
open Rewrite;;
open Alpha;;
open Beta;;
open Printer;;
open Unfold;;


let rec unfold_beta_red te def =
  (*printf "unfold_beta_red: "; print_term te VarMap.empty; printf "\n"; flush stdout;*)
  let te' = (unfold_term te def) in
    if (te = te') then
      te else
	let te'' = (beta_red te' def) in
        if (te'' = te') then
          te'
        else
          unfold_beta_red te'' def
;;
