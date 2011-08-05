open Lisp
open Printf

let main () =
    try (
    
    let filename = Sys.argv.(1) in
    let session = LispLang.empty_session () in
    LispLang.proceed_file session filename
    
  ) with
      | Invalid_argument _ -> interp_stdin (init_ctxt ())
      | LispLang.Exception err -> printf "%s\n" (LispLang.error2string err)
;;

main ()
