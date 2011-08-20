(*
  This file is part of Mymms.

  Mymms is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  Mymms is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with Mymms.  If not, see <http://www.gnu.org/licenses/>.

  Copyright (C) 2008 Nicolas Marti
*)

#include "../../../config"

open Array;;
open String;;

open Printf;;
open Printer;;

open Varmap;;
open Varset;;

open Kernel;;

open State;;
open Extstate;;
open Command;;

open String;;

open Marshal;;

open State;;
open Extinit;;
open Oraclesinit;;

open MN;;
open MZ;;
open MQ;;
open Mfloat;;

open Num;;
open Big_int;;

open Extinit;;
open Command;;
open Oraclesinit;;
open Sys;;

open Def;;

open Lexing;;

open Output;;

#ifdef PYTHON
open Python;;
#endif

(*************************************************************)

let rec interactive () =
  let lexbuf = (Lexing.from_channel stdin) in
  try     
      while true do 
        printf "Kernel < "; flush stdout;
        Parser.input Lexer.token lexbuf;
	if (List.length output_st.normal > 0) then printf "%s\n\n" (String.concat "" (List.rev output_st.normal)) else ();
	if (List.length output_st.error > 0) then printf "%s\n\n" (String.concat "" (List.rev output_st.error)) else ();
	if (List.length output_st.debug > 0) then printf "%s\n" (String.concat "" (List.rev output_st.debug)) else ();
	flush stdout;
	init_output ()	
      done
  with 
      _ -> printf "parsing error (l: %d, c: %d)!\n\n" (lexbuf.lex_curr_p.pos_lnum) (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol); flush stdout; interactive ();
        
;;

let rec webdemo () =
  let lexbuf = Lexing.from_channel stdin in
    try 
      Parser.inputs Lexer.token lexbuf
	  
    with
      | Parsing.Parse_error -> printf "parsing error (l: %d, c: %d)!\n\n" (lexbuf.lex_curr_p.pos_lnum) (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol); exit 0
          
;;

let rec computefile filechannel =
  let lexbuf = Lexing.from_channel filechannel in
    try 
      Parser.inputs Lexer.token lexbuf;
	  
    with
      | Parsing.Parse_error -> printf "parsing error (l: %d, c: %d)!\n\n" (lexbuf.lex_curr_p.pos_lnum) (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol); exit 0
          
;;
    
(*************************************************************)

let main () =

  (* Init The state with the standard library *)
  pushst2inst1 state.tpck ext_typechecker_state ;
  oracle_init ();

  try (
    
    let cmd = Sys.argv.(1) in
      
      match cmd with
	  
	| "-f" -> (
	    
	    try (
	      
	      let filename = Sys.argv.(2) in
	      let filechannel = open_in filename in
		computefile filechannel
		  
	    )  with
	      | Invalid_argument _ -> printf "Format: %s %s <file>\n\n" (Sys.argv.(0)) (Sys.argv.(1))
	  )

	| "-o" -> (

	    try (
	      
	      let filename = Sys.argv.(2) in
		
		try (
		  
		  let filechannel = open_in filename in
		    computefile filechannel;
		    
		    if (List.length state.prooftree = 0 ) then (
		      if (List.length state.variable = 0) then (
		    
			let nstate = empty_state () in
			  
			  (
			    List.fold_left (
			      
			      fun acc hd ->
				
				match hd with
				  | HistDef -> (
				      
				      pushst2inst1 nstate (List.hd state.defhist);
				      state.defhist <- List.tl state.defhist
					
				    )
				  | HistRequired -> (
				      
				      state.defhist <- List.tl state.defhist
					
				    )
				  | _ -> ()			    
				      
			    ) () state.hist 
			      
			      
			  );
			  
			  let filename2 = String.sub filename 0 (String.index filename '.') in
			    
			  let out = open_out_bin (concat "" (filename2 :: ".mo" :: [])) in
			    
			    Marshal.to_channel out (List.flatten state.required, nstate) (No_sharing :: Closures :: []);
			    
			    close_out out;
			    
		      ) else (

			printf "There is a pending variable !!\n"

		      )
		    ) else
		      printf "There is a pending proof !!\n"
		      
		)  with
		  | _ -> printf "Error!!\n\n"
	    ) with
	      | _ -> printf "Format: %s %s <file>\n\n" (Sys.argv.(0)) (Sys.argv.(1))
	  )

	| "-c" -> (

	    try (
	      
	      let _ = Sys.argv.(2) in
	    
		printf "Compilation into executable not yet implemented\n\n"	
		
		
	    ) with
	      | _ -> printf "Format: %s %s <file>\n\n" Sys.argv.(0) Sys.argv.(1)
	  )

	| "-w" -> (

	    webdemo ()

	  )

#ifdef PYTHON
	| "-p" -> mpython ()
#endif
	| _ ->

	    printf "Format: %s [option]\n(if no options then interactive shell)\nOption:\n-w: webdemo mode\n-f <file>: compute the file\n-o <file>: compile the file into a Mymms object\n-c <file>: compile a file into an executable\n-p [file]: run the python virtual machine with Mymms\n\n" (Sys.argv.(0))
    
    
  ) with
      Invalid_argument _ -> (interactive ()); exit 0

;;


init_ext ();
main ()
;;
