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

let test_term s = 
  Format.eprintf "input=%S@." s;
  let stream = Trepparser.Stream.from_string ~filename:"stdin" s in
  match (parse_term (Position.File.top "test")) stream with
  | Result.Ok (res, _) -> 
      printbox (token2box (term2token res InAs) 400 2)
  | Result.Error (pos, s) ->
      Format.eprintf "%a: syntax error: %s@." Position.File.format pos s;
      raise Exit
;;

let _ = test_term "Type";;

let _ = test_term "x";;

let _ = test_term "_";;

let _ = test_term "List (List Type)";;

let _ = test_term "Nat + List (List Type)";;

let _ = test_term "Nat + List (List Type) - Nat * x";;

let _ = test_term "Nat + (List (List Type) - Nat)";;
