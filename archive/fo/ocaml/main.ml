let main () =
  let filename = try Sys.argv.(1) with
      Invalid_argument _ -> let lexbuf = Lexing.from_channel stdin in (*try *) Grammar.input Lexer.token lexbuf; exit 0;
  in
  let filechannel = open_in filename in
  let lexbuf = Lexing.from_channel filechannel in
    (*try *)
    Grammar.input Lexer.token lexbuf
      (*with
        Parsing.Parse_error -> print_string "parsing error\n"; exit 0*)
;;

main ();;
