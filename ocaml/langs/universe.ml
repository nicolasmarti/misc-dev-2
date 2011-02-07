open Pprinter;;
open Listext;;
open Varset;;

type name = string
;;

type univ_level =
  | Zero
  | Level of name
  | Succ of univ_level
  | Max of univ_level list
;;

type univ_level_constraint =
  | UEq of univ_level * univ_level
  | ULt of univ_level * univ_level
;;


let rec univ_level2token (ul: univ_level) : token list =
  match ul with
    | Zero -> (Verbatim "0") :: []
    | Level n -> (Verbatim n) :: []
    | Succ ul -> (univ_level2token ul) @ (Verbatim " + 1") :: []
    | Max uls ->
	(Verbatim "max(") :: (Box (
				concatenate
				  (Verbatim " ,")
				  (List.map (
				     fun hd ->
				       univ_level2token hd
				   ) uls)
			      )
			     ):: (Verbatim ")") :: []
;;

let rec univ_level_constraint2token (ulc: univ_level_constraint) : token list =
  match ulc with
    | UEq (ul1, ul2) ->
	(univ_level2token ul1) @ (Verbatim " == ") :: (univ_level2token ul2)
    | ULt (ul1, ul2) ->
	(univ_level2token ul1) @ (Verbatim " < ") :: (univ_level2token ul2)
;;

let univ_level_constraint2token (ulc: univ_level_constraint list) : token list =
  concatenate
    (Verbatim " /\\ ")
    (List.map (
       fun hd ->
	 univ_level_constraint2token hd
     ) ulc
    )
;;

let pprintunivconstraints l =
  let t = univ_level_constraint2token l in
  let t = Box t in
  let b = token2box t 80 2 in
    printbox b
;;

let rec ul_var (ul: univ_level) : VarSet.t =
  match ul with
    | Level s -> VarSet.singleton s
    | Succ l -> ul_var l
    | Max l -> List.fold_left (fun acc hd ->
				 acc +++ (ul_var hd)
			      ) VarSet.empty l
    | _ -> VarSet.empty
;;

let rec ulc_var (ulc: univ_level_constraint) : VarSet.t =
  match ulc with
    | UEq (ul1, ul2) -> (ul_var ul1) +++ (ul_var ul2)
    | ULt (ul1, ul2) -> (ul_var ul1) +++ (ul_var ul2)
;;
	
