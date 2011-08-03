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
open Str;;
open Buffer;;
open Parser;;


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

let parseintrule = (regexp "[0-9]+", fun (s:string) -> int_of_string s)
;;

type expr =
  | Val of int
  | Lazy of expr
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
      | Lazy e -> print_expr e; printf "&"
      | Plus (e1, e2) -> printf "("; print_expr e1; printf " + "; print_expr e2; printf ")"
      | Minus (e1, e2) -> printf "("; print_expr e1; printf " - "; print_expr e2; printf ")"
      | Mult (e1, e2) -> printf "("; print_expr e1; printf " * "; print_expr e2; printf ")"
      | Div (e1, e2) -> printf "("; print_expr e1; printf " / "; print_expr e2; printf ")"
      | Exp (e1, e2) -> printf "("; print_expr e1; printf " ^ "; print_expr e2; printf ")"
;;

let prefixes: (string, (priority * (expr -> expr))) Hashtbl.t = Hashtbl.create 10;;
Hashtbl.add prefixes "-" (2, fun x -> Neg x);;

let postfixes: (string, (priority * (expr -> expr))) Hashtbl.t = Hashtbl.create 10;;
Hashtbl.add postfixes "&" (3, fun x -> Lazy x);;

let infixes: (string, (priority * associativity * (expr -> expr -> expr))) Hashtbl.t = Hashtbl.create 10;;
Hashtbl.add infixes "+" (1, LeftAssoc, fun x y -> Plus (x, y));;
Hashtbl.add infixes "-" (2, LeftAssoc, fun x y -> Minus (x, y));;
Hashtbl.add infixes "*" (4, RightAssoc, fun x y -> Mult (x, y));;
Hashtbl.add infixes "/" (4, RightAssoc, fun x y -> Div (x, y));;


let valparser : expr Parser.parsingrule = 
  (tryrule ((fun _ x -> Val x) |> (spaces) >> (applylexingrule parseintrule)))
  <|> (tryrule ((fun _ x -> Val x) |> (spaces) >> (applylexingrule parseintrule)))

;;


let myp : expr opparser = {
  primary = valparser;
  prefixes = prefixes;
  infixes = infixes;
  postfixes = postfixes;
};;

let text = "- 1 + - 1& * - 10 + 9& * 4 &";;
let lines = stream_of_string text;;
let pb = build_parserbuffer lines;;

let rec random size = 
  let key = if size = 0 then 0 else Random.int 6 in
  match key with
  | 0 -> string_of_int (Random.int 10)
  | 1 -> "- " ^ random (size-1) 
  | 2 -> "(" ^ random (size-1) ^ ")"
  | 3 -> random (size-1) ^ " + " ^ random (size-1)
  | 4 -> random (size-1) ^ " - " ^ random (size-1)
  | 5 -> random (size-1) ^ " * " ^ random (size-1)
  | _ -> assert false
;;

let test s =
try 
  printf "----------\ns = %s\n" s;
  let lines = stream_of_string s in
  let pb = build_parserbuffer lines in
  let mexpr = (opparse myp) pb in
    print_expr mexpr;
    printf "\n\n";
with
  | NoMatch -> 
      printf "error:%s\n\n" (errors2string pb);
      printf "%s\n\n" (markerror pb);
      printf "begin pointer = %d\n\n" pb.beginpointer;
;;

let _ = 
  for i = 0 to 100 do
    test (random 20)
  done;
;;
