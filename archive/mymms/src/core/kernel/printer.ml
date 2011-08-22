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
open Def;;
open Term;;
open Varset;;
open Listext;;
open Varmap;;
open Definition;;
open Output;;

let rec print_listint l =
  match l with
    | [] -> printf "";
    | hd :: tl -> 
        printf "%d" hd;
        match tl with
          | [] -> printf "";
          | _ -> printf ", "; print_listint tl
;;

let rec string_of_listint l =
  match l with
    | [] -> ""
    | hd :: tl -> 
        concat "" ((string_of_int hd) ::
                      (match tl with
                        | [] -> "" :: []
                        | _ -> ", " :: string_of_listint tl :: []
                      )
        )
;;

let rec string_of_listofvar l =
  match l with
    | [] -> ""
    | hd :: tl ->
        match tl with
          | [] -> hd
          | _ -> concat "" (hd :: " " :: string_of_listofvar tl :: [])
;;

let rec string_of_term t impl =
  match t with
    | Avar -> "_"

    | Obj o ->
        (*concat "" ("{" :: o#get_name :: "}" :: [] )*)
        o#pprint [] impl
    | Cste c -> (
        (*concat "" ("[" :: c :: "]" :: [])w*)
        (*c*)
	let path = defname2path c in
	let c = List.nth path (List.length path - 1) in
	  (*concat "" ("[" :: c :: "]" :: [])*)
	  concat "" (c :: [])
      )
    | Var x -> x

    | Let (x,t1,t2) -> 
        concat "" ("let " :: x :: ":= " :: string_of_term t1 impl :: " in " :: string_of_term t2 impl :: [])

    | Lambda (x,t1,t2) -> 
        concat "" ("\\ (" :: x :: ": " :: string_of_term t1 impl :: "). (" :: string_of_term t2 impl :: ")" :: [])
    | Forall (x,t1,t2) -> 
        if (not (VarSet.subset (VarSet.singleton x) (term_fv t2 VarSet.empty))) then
          concat "" (
            (
              match t1 with
                | Obj o -> string_of_term t1 impl 
                | Cste c -> string_of_term t1 impl 
                | Var x -> string_of_term t1 impl 
                | Type -> string_of_term t1 impl 
                | _ -> concat "" ("(" :: string_of_term t1 impl :: ")" ::[])

            )
            :: " -> " :: string_of_term t2 impl:: [])
        else
          concat "" ("V (" :: x :: ": "  :: string_of_term t1 impl :: "). " :: string_of_term t2 impl :: [])
    | Phi (x,largs, ty, li, body) -> 
        concat "" ("! (" :: x  :: ", (" :: string_of_listvarterm largs impl :: "), " :: string_of_term ty impl :: string_of_term  body impl :: [])
    | Ind (x,largs, ty, lcons) -> 
        concat "" ("I (" :: x  :: ", " :: string_of_listvarterm largs impl :: ", " :: string_of_term ty impl :: "). (" :: string_of_listterm lcons impl :: ")" :: [])
    | App (t1, t2) -> 
        concat "" ((
          let t2 = (
            match t1 with
              | Cste n -> (
                  try 
                    let l = VarMap.find n impl in
                      nth_tail l t2
                  with
                    | _ -> t2
                )
              | _ -> t2
          ) in (            
            match t1 with
              | Obj o -> 
                  (
                    match t2 with
                      | [] -> string_of_term t1 impl
                      | _ -> o#pprint t2 impl
                  )
                    
              | Cste o -> 
                  (
                    match t2 with
                      | [] -> string_of_term t1 impl
                      | _ -> concat "" (string_of_term t1 impl :: " " :: string_of_listterm2 t2 impl :: [])
                  )
                    
              | Var _ -> (
                  match t2 with
                    | [] -> string_of_term t1 impl
                    | _ -> concat "" (string_of_term t1 impl :: " " :: string_of_listterm2 t2 impl :: [])
                )
              | _ -> (
                  match t2 with
                    | [] -> string_of_term t1 impl
                    | _ -> concat "" ("(" :: string_of_term t1 impl :: ") " :: string_of_listterm2 t2 impl :: [])
                )
          )
        ) :: [])
    | Match (t1, l1, t2, ind) -> 
        concat "" ("match " ::
                      (match t1 with
                        | Cste _ -> string_of_term t1 impl :: []
                        | Var _ -> string_of_term t1 impl :: []
                        | Obj _ -> string_of_term t1 impl :: []
                        | _ -> "(" :: string_of_term t1 impl :: ")" :: []
                      ) @ (
                        
                        match t2 with
                          | None -> ""
                          | Some t2 ->
                              concat "" (" return " :: string_of_term t2 impl :: [])

                      ) ::
                      " with (" :: string_of_listterm l1 impl :: ")" :: [])
    | AdvMatch (t1, l1, t2) -> 
        concat "" ("match " ::
                      (match t1 with
                        | Cste _ -> string_of_term t1 impl :: []
                        | Var _ -> string_of_term t1 impl :: []
                        | Obj _ -> string_of_term t1 impl :: []
                        | _ -> "(" :: string_of_term t1 impl :: ")" :: []
                      ) @ (
                        
                        match t2 with
                          | None -> ""
                          | Some t2 ->
                              concat "" (" return " :: string_of_term t2 impl :: [])

                      ) ::
                      " with (" :: string_of_listtermterm l1 impl :: ")" :: [])

    | Cons (n,l) -> concat "" ("cons " :: string_of_int n :: " of (" :: string_of_term l impl :: ")" :: [])
    | Type -> "Type"
and string_of_listterm l impl =
  match l with
    | [] -> ""
    | hd :: tl ->
        (concat ""
            (string_of_term hd impl :: 
                (match tl with
                  | [] -> "" :: []
                  | _ -> ", " :: string_of_listterm tl impl :: []
                ) 
            )
        )
and string_of_listterm2 l impl =
  match l with
    | [] -> ""
    | hd :: tl -> 
        match hd with
          | App (_, _) -> (
              match tl with
                | [] -> concat "" ("(" :: string_of_term hd impl :: ")" :: [])
                | _ -> concat "" ("(" :: string_of_term hd impl :: ") " :: string_of_listterm2 tl impl :: [])
            )
          | Match (_,_,_,_) -> (
              match tl with
                | [] -> concat "" ("(" :: string_of_term hd impl :: ")" :: [])
                | _-> concat "" ("(" :: string_of_term hd impl :: ") " :: string_of_listterm2 tl impl :: [])
            )
          | Forall (_, _, _) -> (
              match tl with
                | [] -> concat "" ("(" :: string_of_term hd impl :: ")" :: [])
                | _ -> concat "" ("(" :: string_of_term hd impl :: ") " :: string_of_listterm2 tl impl :: [])
            )
          | _ -> 
              match tl with
                | [] -> string_of_term hd impl
                | _ -> concat "" (string_of_term hd impl :: " " :: string_of_listterm2 tl impl :: [])
and string_of_listvarterm l impl =
  match l with
    | [] -> ""
    | (hd1, hd2) :: tl -> 
        concat "" ("("  :: hd1 :: ": " :: string_of_term hd2 impl :: ")" ::
                      (match tl with
                        | [] -> "" :: []
                        | _ -> ", " :: string_of_listvarterm tl impl ::[]
                      )
        )
and string_of_listtermterm l impl =
  match l with
    | [] -> ""
    | (hd1, hd2) :: tl -> 
        concat "" ("("  :: string_of_term hd1 impl :: " ==> " :: string_of_term hd2 impl :: ")" ::
                      (match tl with
                        | [] -> "" :: []
                        | _ -> ", " :: string_of_listtermterm tl impl ::[]
                      )
        )

;;

let rec print_term t impl =
  printf "%s" (string_of_term t impl)
and print_listterm l impl =
  printf "%s" (string_of_listterm l impl)
and print_listterm2 l impl =
  printf "%s" (string_of_listterm2 l impl)
and print_listvarterm l impl =
  printf "%s" (string_of_listvarterm l impl)
and print_listtermterm l impl =
  printf "%s" (string_of_listtermterm l impl)
;;


let string_of_nature nature =
  match nature with
    | TYPE -> "TYPE"
    | FUNCTION -> "FUNCTION"
    | DATA -> "DATA" 
    | UNKNOWN -> "UNKNOWN"
;;
