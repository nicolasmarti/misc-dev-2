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

open Stream;;
open Printf;;
open Parser;;
open Str;;
open Buffer;;


(*****************************************************)

(* Test *)


let line_stream_of_channel channel =
  Stream.from
    (fun _ ->
       try Some (input_line channel) with End_of_file -> None)

let stream_of_string s =
  Stream.from
    (fun x ->
       match x with
	 | 0 -> Some s
	 | _ -> None
    )

let parseintrule : int lexingrule = (regexp "[0-9]+", fun (s:string) -> int_of_string s)
;;

type expr =
  | Val of int
  | Neg of expr
  | Plus of expr * expr
  | Minus of expr * expr
  | Mult of expr * expr
  | Div of expr * expr
  | Exp of expr * expr
;;

let rec print_expr (e: expr) =
    match e with
      | Val i -> printf "%d" i
      | Neg e ->  printf "(- "; print_expr e; printf ")"
      | Plus (e1, e2) -> printf "("; print_expr e1; printf " + "; print_expr e2; printf ")"
      | Minus (e1, e2) -> printf "("; print_expr e1; printf " - "; print_expr e2; printf ")"
      | Mult (e1, e2) -> printf "("; print_expr e1; printf " * "; print_expr e2; printf ")"
      | Div (e1, e2) -> printf "("; print_expr e1; printf " / "; print_expr e2; printf ")"
      | Exp (e1, e2) -> printf "("; print_expr e1; printf " ^ "; print_expr e2; printf ")"
;;

let prefixes: (string, (priority * (expr -> expr))) Hashtbl.t = Hashtbl.create 10;;
Hashtbl.add prefixes "-" (2, fun x -> Neg x);;

let infixes: (string, (priority * associativity * (expr -> expr -> expr))) Hashtbl.t = Hashtbl.create 10;;
Hashtbl.add infixes "+" (1, Left, fun x y -> Plus (x, y));;
Hashtbl.add infixes "-" (2, Left, fun x y -> Minus (x, y));;
Hashtbl.add infixes "*" (3, Right, fun x y -> Mult (x, y));;
Hashtbl.add infixes "/" (3, Right, fun x y -> Div (x, y));;

let valparser : expr parsingrule = 
  (tryrule ((fun _ x -> Val x) |> (spaces) >> (applylexingrule parseintrule)))
  <|> (tryrule ((fun _ x -> Val x) |> (spaces) >> (applylexingrule parseintrule)))

;;


let myp : expr opparser = {
  primary = valparser;
  prefixes = prefixes;
  infixes = infixes;
};;

let text = "- 1 + - 1 * - 10 + 9";;
let lines = stream_of_string text;;
let pb = build_parserbuffer lines;;

try 
  let mexpr = (opparse myp) pb in
    printf "%s\n" text;
    print_expr mexpr;
    printf "\n\n";
with
  | NoMatch -> 
      printf "error:%s\n\n" (errors2string pb);
      printf "%s\n\n" (markerror pb);
;;

