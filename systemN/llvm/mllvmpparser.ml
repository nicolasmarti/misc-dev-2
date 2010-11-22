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
let rec cmd0_pprinter (te: cmd0) (paren: bool) : token =
  match te with
    | Unit -> Verbatim "()"
    | Return ty -> Box ([Verbatim "Return"; Space 1; cmd0_pprinter te true])
;;

let rec cmd0_parser : cmd0 parsingrule =
  fun pb -> (
    ( (fun x -> x) |> spaces >> keyword "()" Unit )
    <|> ( ( fun _ x -> Return x ) |> (spaces >>> keyword "return" ()) >> expr0_parser)
  ) pb
and expr0_parser : expr0 parsingrule =
  raise (Failure "Not Yet Implemented")
and cste_parser : cste parsingrule =
  raise (Failure "Not Yet Implemented")
;;
