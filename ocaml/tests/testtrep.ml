open Trep;;
open Trepparser;;
open Trepprinter;;
open Def;;
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
    raise Pervasives.Exit
;;


let test_term = test_parse_print (fun x -> parse_term (Position.File.top "test") x) (fun res -> (token2box (term2token res InAs) 400 2))
;;

let test_pattern = test_parse_print (fun x -> parse_pattern (Position.File.top "test") x) (fun res -> (token2box (pattern2token res InAs) 400 2))
;;

let test_declaration = test_parse_print (fun x -> parse_declaration (Position.File.top "test") x) (fun res -> (token2box (declaration2token res) 400 2))
;;

let _ = test_pattern "a+b" ;;

let _ = test_term "x";;

let _ = test_term "x";;

let _ = test_term "_";;

let _ = test_term "List (List Type)";;

let _ = test_term "Nat + List (List Type)";;

let _ = test_term "(Nat + List (List Type) - Nat * x) - d";;

let _ = test_term "Nat + (List (List Type) - Nat)";;

let _ = test_term "(*) x";;

let _ = test_term "let x := y; f@(x + y) a r := doudou; g@(x+y) := sdf in z";;

let _ = test_term "case f x of | _ := x | f x := y" ;;

let _ = test_term "if x + y then x - r else x - z" ;;

let _ = test_term "\\ A (a b :: A) {f :: B} [H :: Num A] -> a + b" ;;

let _ = test_term "A -> (a b :: A) -> {f :: B} -> [H :: Num A] -> a + b" ;;

let _ = test_declaration "(+) :: {A} -> [Num A] -> A -> A -> A" ;;

let _ = test_declaration "(+) {Type} [isNum {Type} plus] a b :=  plus a b" ;;

let _ = test_declaration "(+) {Type} [isNum {Type} plus] a b :=  plus a b  where Num :: Type -> Type" ;;

let _ = test_declaration "inductive List A :: Type := nil :: List A | cons :: A -> List A -> List A" ;;

let ctxt = ref empty_ctxt;;

let test_parse_typecheck_declaration s = 
  Format.eprintf "input=%S@." s;
  let stream = Trepparser.Stream.from_string ~filename:"stdin" s in
  match parse_declaration (Position.File.top "test") stream with
  | Result.Ok (res, _) ->
    let decl = push_declaration ctxt res in
    printbox (token2box (declaration2token decl) 400 2)
  | Result.Error (pos, s) ->
    Format.eprintf "%a: syntax error: %s@." Position.File.format pos s;      
    raise Pervasives.Exit
;;


let _ =  test_parse_typecheck_declaration "Bool :: Type";;
let _ =  test_parse_typecheck_declaration "True :: Bool";;
let _ =  test_parse_typecheck_declaration "False :: Bool";;
