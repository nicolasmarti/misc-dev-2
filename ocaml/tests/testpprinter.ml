(*

  This file is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  This file is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this file.  If not, see <http://www.gnu.org/licenses/>.

  Copyright (C) Nicolas Marti
*)

open Pprinter;;
open Printf;;

let test = 
  Box [Verbatim "doudou"; Space 2;Verbatim "doudou"]
;;

printbox (token2box test 20 2);;
printf "\n\n";;

printbox (token2box test 10 2);;
printf "\n\n";;

let test = 
  Box [Box [Verbatim "b11"; Newline;Verbatim "b12"]; Space 2;Verbatim "doudou1"; Space 2;Verbatim "doudou2"; Space 4; Box [Verbatim "a11"; Space 2;Verbatim "a21"]]
;;

printbox (token2box test 20 2);;
printf "\n\n";;

let test2 = 
  Box [Box[Box [Verbatim "b11"; Newline;Verbatim "b12"]; Space 2;Verbatim "doudou1"; Space 2;Verbatim "doudou2"; Space 4; IBox [Verbatim "a11"; Space 2;Verbatim "a21"]]]
;;

printbox (token2box test2 10 2);;
printf "\n\n";;
