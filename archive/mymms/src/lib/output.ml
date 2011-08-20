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

type output_state = {
  mutable normal : string list;
  mutable error: string list;
  mutable debug: string list;
};;


let output_st = {
  normal = [];
  error = [];
  debug = [];
};;

let init_output () =
  output_st.normal <- [];
  output_st.error <- [];
  output_st.debug <- [];
;;

let print s =
  output_st.normal <- s :: output_st.normal
;;

let print_error s =
  output_st.error <- s :: output_st.error
;;

let print_debug s =
  output_st.debug <- s :: output_st.debug
;;


