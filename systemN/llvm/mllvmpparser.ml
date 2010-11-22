open Mllvm;;
open Parser;;
open Pprinter;;
open Varmap;;

(**********************************)

let rec llvmtype_pprinter (typeenv: llvmtype VarMap.t) (ty: llvmtype) : token =
  match ty with
    | TUnit -> Verbatim "()"
;;

let rec llvmtype_parser : llvmtype parsingrule =
  fun pb ->
    ( (fun x -> x) |> spaces >> keyword "()" TUnit )
      pb
;;

(**********************************)

let rec cmd0_pprinter (te: cmd0) : token =
  match te with
    | Unit -> Verbatim "()"
;;

let rec cmd0_parser : cmd0 parsingrule =
  fun pb ->
    ( (fun x -> x) |> spaces >> keyword "()" Unit )
      pb
;;
