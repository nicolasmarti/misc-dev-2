open Trep;;
open Trepparser;;
open Trepprinter;;

open Planck;;
open Position;;

open Pprinter;;

let test_term s = 
  Format.eprintf "input=%S@." s;
  let stream = Trepparser.Stream.from_string ~filename:"stdin" s in
  match (parse_term (Position.File.top "test")) stream with
  | Result.Ok (res, _) -> 
      printbox (token2box (term2token res) 400 2)
  | Result.Error (pos, s) ->
      Format.eprintf "%a: syntax error: %s@." Position.File.format pos s;
      raise Exit
;;

let _ = test_term "Type";;
