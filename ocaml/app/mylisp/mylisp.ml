open Lisp
open Printf

let main () =
    try (
    
    let filename = Sys.argv.(1) in
    let session = LispLang.empty_session () in
    LispLang.proceed_file session filename
    
  ) with
      | Invalid_argument _ -> 
	printf "mylisp interactive mode\n";
	printf "enter terms then a final <enter> and <CTRL-D> for proceeding\n";
	printf "<CTRL-D> on empty prompt to exit\n";
	printf "--------------------------------\n\n";	
	flush Pervasives.stdout;
	interp_stdin (init_ctxt ())
      | LispLang.Exception err -> printf "%s\n" (LispLang.error2string err)
;;

main ()
