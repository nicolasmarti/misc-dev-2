open Mllvm;;
open Parser;;
open Pprinter;;
open Varmap;;
open Str;;

(**********************************)

let int_lexingrule : int lexingrule = (regexp "[0-9]+", fun (s:string) -> int_of_string s)
;;

let int_parsingrule : int parsingrule = applylexingrule int_lexingrule
;;

(**********************************)

let rec llvmtype_pprinter (typeenv: llvmtype VarMap.t) (ty: llvmtype) : token =
  match ty with
    | TUnit -> Verbatim "()"
    | TInteger i -> Verbatim (String.concat "" ["i"; string_of_int i]) 
;;

let rec llvmtype_parser : llvmtype parsingrule =
  fun pb -> (
    ( (fun x -> x) |> spaces >> keyword "()" TUnit )
    <|> ((fun _ i -> TInteger i) |> (spaces >>> keyword "i" ()) >> int_parsingrule)
  ) pb
;;

(**********************************)
let rec cmd0_pprinter (te: cmd0) : token =
  match te with
    | Unit -> Verbatim "()"
;;

let rec cmd0_parser : cmd0 parsingrule =
  fun pb -> (
    ( (fun x -> x) |> spaces >> keyword "()" Unit )

  ) pb
;;
