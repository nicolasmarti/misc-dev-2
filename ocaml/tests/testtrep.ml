open Trep;;
open Trepparser;;
open Trepprinter;;

open Planck;;
open Position;;

open Pprinter;;
open Spotlib.Spot;;
open Op_prec;;

let _ = 
  Hashtbl.replace_list Op_prec.tbl [
    "+",  { prec = 2.0; kind = `Infix `Left };
    "-",  { prec = 2.0; kind = `Infix `Left };
    "*",  { prec = 3.0; kind = `Infix `Left };
    "/",  { prec = 3.0; kind = `Infix `Left };
    "~",  { prec = 5.0; kind = `Prefix }; (* unary minus *)
  ]

let test_parse_print parse print s = 
  Format.eprintf "input=%S@." s;
  let stream = Trepparser.Stream.from_string ~filename:"stdin" s in
  match parse stream with
  | Result.Ok (res, _) -> 
      printbox (print res)
  | Result.Error (pos, s) ->
      Format.eprintf "%a: syntax error: %s@." Position.File.format pos s;      
;;


let test_term = test_parse_print (fun x -> parse_term (Position.File.top "test") x) (fun res -> (token2box (term2token res InAs) 400 2))
;;


let _ = test_term "Type";;

let _ = test_term "x";;

let _ = test_term "_";;

let _ = test_term "List (List Type)";;

let _ = test_term "Nat + List (List Type)";;

let _ = test_term "Nat + List (List Type) - Nat * x";;

let _ = test_term "Nat + (List (List Type) - Nat)";;

let _ = test_term "(*) x";;


let _ = test_term "let x := y; f@(x + y) a r := sdf in z";;

