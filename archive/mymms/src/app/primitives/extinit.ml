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

open Varmap;;
open State;;

open MN;;
open MZ;;
open MQ;;
open Mfloat;;
open Marray;;
open Mmatrix;;
open Mstring;;
open MVM;;
open Mutable;;
open MError;;
open Extstate;;

let init_ext () =

  mN_init;
  mZ_init;
  mQ_init;
  mfloat_init;
  marray_init;
  mmatrix_init;
  mstring_init;
  mvm_init;
  mutable_init;
  mError_init;

;;
