(*
  This file is part of Mymm.

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

open Array;;
open String;;

open Printf;;
open Printer;;

open Varmap;;
open Varset;;

open Kernel;;

open State;;
open Command;;

open String;;

open Marshal;;

open State;;
open Oraclesinit;;

open MN;;
open MZ;;
open MQ;;
open Mfloat;;
open Marray;;
open Mstring;;
open Mmatrix;;

open Num;;
open Big_int;;

open Extinit;;
open Command;;
open Oraclesinit;;
open Sys;;

open Def;;

open Pycaml;;

open Lexing;;

open Char;;

open Output;;

let loadaddin file =
  let paths =
    
    try (
      let path = getenv "MYMMS_ADDIN_PATH" in
      let lst = cutstring path ':' in
	
	"."::lst
	  
    ) with 
	
      | _ -> "." :: []	
	  
		
  in
    
    match loadExt file paths with
      | None -> print_error (sprintf "Load: Error (%s)!!\n\n" file);
      | Some _ -> print_error (sprintf "Loaded: %s!!\n\n" file);
;;


(****************************)


(* wraping of poussin functions 
   
   WARNING !!!
   -> no partial exec
   -> term <-> pyobject does not support streaned object

*)


let py2termInt p =
  match pytype p with
    | IntType -> (
	let i = (pyint_asint p) in
	  if (i >= 0) then
	    Some (create_mNTerm (big_int_of_int i))
	  else
	    Some (create_mZTerm (big_int_of_int i))
      )
    | _ -> None
;;

let py2termFloat p =
  match pytype p with
    | FloatType -> Some (create_floatTerm (pyfloat_asdouble p))
    | _ -> None
;;


let term2pyQ t =
  match t with
    | Obj o -> 
	
	if (o#get_type = mQType) then (
	  
	  let o = ((Obj.magic o) :> mQTermObj ) in
	    
	    Some (pyfloat_fromdouble (float_of_num (o#get_value)))	    
	      
	) else 
	  None
    | _ -> None
;;

let term2pyFloat t =
  match t with
    | Obj o -> 
	if (o#get_type = floatType) then (
	  
	  let o = ((Obj.magic o) :> floatTermObj ) in
	    
	    Some (pyfloat_fromdouble (o#get_floatvalue))
	      
	) else 
	  None

    | _ -> None
;;

let term2pyZ t =
  match t with
    | Obj o -> 
	if (o#get_type = mZType) then (
	  
	  let o = ((Obj.magic o) :> mZTermObj ) in
	    
	    Some (pyint_fromint (int_of_big_int (o#get_value)))	    
	      
	) else None
	  
    | _ -> None
;;

let term2pyN t =
  match t with
    | Obj o -> 
	if (o#get_type = mNType) then (
	  
	  let o = ((Obj.magic o) :> mNTermObj ) in
	    
	    Some (pyint_fromint (int_of_big_int (o#get_value)))	    
	      
	) else None
	  
    | _ -> None
;;


let term2pyString t =
  match t with
    | Obj o -> 
	if (o#get_type = stringType) then (
	  
	  let o = ((Obj.magic o) :> stringTermObj ) in
	    
	    Some (pystring_fromstring (o#get_stringvalue))
	      
	) else 
	  None

    | _ -> None
;;

let py2termString p =
  match pytype p with
    | StringType -> Some (create_stringTerm (pystring_asstring p))
    | _ -> None
;;


let term2pyChar t =
  match t with
    | Obj o -> 
	if (o#get_type = charType) then (
	  
	  let o = ((Obj.magic o) :> charTermObj ) in
	    
	    Some (pystring_fromstring (escaped o#get_charvalue))
	      
	) else 
	  None

    | _ -> None
;;

let py2termChar p =
  match pytype p with
    | StringType -> Some (create_charTerm (pystring_asstring p).[0])
    | _ -> None
;;



type python_state = {
  mutable py2term: (pyobject -> term option) list;
  mutable term2py: (term -> pyobject option) list;
};;

let start_state : python_state = {
  py2term = py2termString :: py2termInt :: py2termFloat :: [];
  term2py = term2pyString :: term2pyFloat :: term2pyN :: term2pyZ :: term2pyQ :: [];
};;




let pyobject2term p =
  List.fold_left (fun acc hd ->
		    match acc with
		      | Some _ -> acc
		      | None ->
			  hd p
		 ) None start_state.py2term 
;;

let term2pyobject t =
  List.fold_left (fun acc hd ->
		    match acc with
		      | Some _ -> acc
		      | None ->
			  hd t
		 ) None start_state.term2py
;;

let term2pyfunc t = pywrap_closure
  (

    fun x ->

      let a = pytuple_toarray x in

	let args = 

	  Array.fold_left (
	    
	    fun acc hd ->
	      
	      match (acc, pyobject2term hd) with
		| (Some l, Some t) -> (

		    Some (l @ t::[])

		  )
		| _ -> None
		    
		  
	  ) (Some []) a
	  	    
	in

	  match args with
	    | None -> print_error "pyobject -> largs: error\n"; pyerr_occurred ();
	    | Some largs ->
		
		match check_term "" (App (t, largs)) None state.tpck.def state.tpck.coercion (oracleslist state.tpck.oracles) state.tpck.overload state.tpck.implicite with
		  | None -> print_error "termchecking: error\n"; pyerr_occurred ();
		  | Some (te, ty) ->

		      (*match interpretation te (Some ty) with*)
		      match vmcompute te (Some ty) with
			| None -> print_error "compute: error\n"; pyerr_occurred ();
			| Some (te, ty) ->
			    match (term2pyobject te) with
			      | None -> print_error "res -> pyobject: error\n"; pyerr_occurred ();
			      | Some res -> res

  )
;;

let mymms2python = pywrap_closure
  ( 
    fun x ->
      init_output ();      
      let a = pytuple_toarray x in

	try (
	  
	  let te = pystring_asstring a.(0) in

	  let lexbuf = Lexing.from_string te in
	    try 
	      let te = Parser.term Lexer.token lexbuf in

	      	match check_term "" te None state.tpck.def state.tpck.coercion (oracleslist state.tpck.oracles) state.tpck.overload state.tpck.implicite with
		  | None -> print_error "termchecking error\n"; pyerr_occurred ();
		  | Some (te, ty) ->
		      
		      term2pyfunc te     

		  
	    with
	      | Parsing.Parse_error -> print_error (sprintf "parsing error (l: %d, c: %d)!\n\n" (lexbuf.lex_curr_p.pos_lnum) (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol)); pyerr_occurred ();
  


	) with
	  | _ -> print_error "mymms2python error !!!\n"; pyerr_occurred ();


  );;




(****************************)

let simpl = pywrap_closure
  ( 
    fun x ->
      init_output ();
      let a = pytuple_toarray x in

	try (

	  let te = pyunwrap_value a.(0) in
	    
	  let args = 

	    Array.fold_left (
	      
	      fun acc hd ->
		
		acc @ (pyunwrap_value hd)::[]

	    ) [] (Array.sub a 1 (Array.length a - 1))

	  in 

	  let te = App (te, args) in

	    match simpl_term "" te None state.tpck.def state.tpck.coercion (oracleslist state.tpck.oracles) state.tpck.overload state.tpck.implicite with
	      | None -> print_error "simplification error\n"; pyerr_occurred ();
	      | Some (te, ty) ->
		  
		  let a = Array.of_list ((pywrap_value te)::(pywrap_value ty)::(pystring_fromstring (string_of_term te state.tpck.implicite))::(pystring_fromstring (string_of_term ty state.tpck.implicite))::[]) in
		    pytuple_fromarray a
	    



	) with
	  | _ -> print_error "simpl error !!!\n"; pyerr_occurred ();

  
  )
;;


let simpl2 = pywrap_closure
  ( 
    fun x ->
      init_output ();
      let a = pytuple_toarray x in

	try (

	  let te = pyunwrap_value a.(0) in

	  let args = pytuple_toarray a.(1) in
	    
	  let args = 

	    Array.fold_left (
	      
	      fun acc hd ->
		
		acc @ (pyunwrap_value hd)::[]

	    ) [] args

	  in 

	  let te = App (te, args) in

	    match simpl_term "" te None state.tpck.def state.tpck.coercion (oracleslist state.tpck.oracles) state.tpck.overload state.tpck.implicite with
	      | None -> print_error "simplification error\n"; pyerr_occurred ();
	      | Some (te, ty) ->
		  
		  let a = Array.of_list ((pywrap_value te)::(pywrap_value ty)::(pystring_fromstring (string_of_term te state.tpck.implicite))::(pystring_fromstring (string_of_term ty state.tpck.implicite))::[]) in
		    pytuple_fromarray a
	    



	) with
	  | _ -> print_error "simpl error !!!\n"; pyerr_occurred ();

  
  )
;;

let interp = pywrap_closure
  ( 
    fun x ->
      init_output ();
      let a = pytuple_toarray x in

	try (

	  let te = pyunwrap_value a.(0) in
	    
	  let args = 

	    Array.fold_left (
	      
	      fun acc hd ->
		
		acc @ (pyunwrap_value hd)::[]

	    ) [] (Array.sub a 1 (Array.length a - 1))

	  in 

	  let te = App (te, args) in

	    match interpretation te None with
	      | None -> print_error "interpretation error\n"; pyerr_occurred ();
	      | Some (te, ty) ->
		  
		  let a = Array.of_list ((pywrap_value te)::(pywrap_value ty)::(pystring_fromstring (string_of_term te state.tpck.implicite))::(pystring_fromstring (string_of_term ty state.tpck.implicite))::[]) in
		    pytuple_fromarray a
	    



	) with
	  | _ -> print_error "interp error !!!\n"; pyerr_occurred ();

  
  )
;;

let interp2 = pywrap_closure
  ( 
    fun x ->
      init_output ();
      let a = pytuple_toarray x in

	try (

	  let te = pyunwrap_value a.(0) in
	    
	  let args = pytuple_toarray a.(1) in
	    
	  let args = 

	    Array.fold_left (
	      
	      fun acc hd ->
		
		acc @ (pyunwrap_value hd)::[]

	    ) [] args

	  in 

	  let te = App (te, args) in

	    match interpretation te None with
	      | None -> print_error "interpretation error\n"; pyerr_occurred ();
	      | Some (te, ty) ->
		  
		  let a = Array.of_list ((pywrap_value te)::(pywrap_value ty)::(pystring_fromstring (string_of_term te state.tpck.implicite))::(pystring_fromstring (string_of_term ty state.tpck.implicite))::[]) in
		    pytuple_fromarray a
	    



	) with
	  | _ -> print_error "interp error !!!\n"; pyerr_occurred ();

  
  )
;;


(****************************)

let pytypecheck = pywrap_closure
  ( 
    fun x ->
      
      init_output ();
      let a = pytuple_toarray x in

	try (
	  
	  let te = pystring_asstring a.(0) in

	  let lexbuf = Lexing.from_string te in
	    try 
	      let te = Parser.term Lexer.token lexbuf in

	      	match check_term "" te None state.tpck.def state.tpck.coercion (oracleslist state.tpck.oracles) state.tpck.overload state.tpck.implicite with
		  | None -> print_error "termchecking error\n"; pyerr_occurred ();
		  | Some (te, ty) ->
		      
		      let a = Array.of_list ((pywrap_value te)::(pywrap_value ty)::(pystring_fromstring (string_of_term te state.tpck.implicite))::(pystring_fromstring (string_of_term ty state.tpck.implicite))::[]) in
			pytuple_fromarray a

		  
	    with
	      | Parsing.Parse_error -> print_error (sprintf "parsing error (l: %d, c: %d)!\n\n" (lexbuf.lex_curr_p.pos_lnum) (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol)); pyerr_occurred ();
  


	) with
	  | _ -> print_error "pytypecheck error !!!\n"; pyerr_occurred ();


  );;

(****************************)

let mymmsrequire = pywrap_closure
  ( 
    fun x ->
      init_output ();      
      let a = pytuple_toarray x in

	try (
	  
	  let te = pystring_asstring a.(0) in

	    print_debug (sprintf "mymmsrequire: %s\n" te); 
	    manageCommand (CmdControl (Require te)); flush stdout;
	    pytuple_empty
	    

	) with
	  | e -> print_error "mymmsrequire !!!\n"; raise e; (*pyerr_occurred ();*)


  );;

let mymmsload = pywrap_closure
  ( 
    fun x ->
      init_output ();
      let a = pytuple_toarray x in

	try (
	  
	  let te = pystring_asstring a.(0) in

	    print_debug (sprintf "mymmsload: %s\n" te); 
	    manageCommand (CmdControl (Load te)); flush stdout;
	    pytuple_empty
	    

	) with
	  | e -> print_error "mymmsload !!!\n"; raise e; (*pyerr_occurred ();*)


  );;

(****************************)

let addinload = pywrap_closure
  ( 
    fun x ->
      init_output ();
      let a = pytuple_toarray x in

	try (
	  
	  let file = pystring_asstring a.(0) in

	    loadaddin file;
	    pytuple_empty
	    

	) with
	  | e -> print_error "addinload !!!\n"; raise e; (*pyerr_occurred ();*)


  );;

(****************************)

let getnormaloutput = pywrap_closure
  ( 
    fun x ->

      let s = String.concat "" (List.rev output_st.normal) in
	pystring_fromstring s

  );;

let getdebugoutput = pywrap_closure
  ( 
    fun x ->

      let s = String.concat "" (List.rev output_st.debug) in
	pystring_fromstring s

  );;

let geterroroutput = pywrap_closure
  ( 
    fun x ->

      let s = String.concat "" (List.rev output_st.error) in
	pystring_fromstring s

  );;

(****************************)

let mymmscommand = pywrap_closure
  ( 
    fun x ->
      init_output ();
      let a = pytuple_toarray x in
      let cmd = pystring_asstring a.(0) in
	(*printf "%s\n\n" cmd; flush stdout;*)
	let lexbuf = (Lexing.from_string cmd) in
	try 		
	  Parser.input Lexer.token lexbuf;
	  pytuple2 (pyint_fromint (lexbuf.lex_curr_p.pos_lnum), pyint_fromint (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol))	      
	with 
	  | _ -> print_error (sprintf "parsing error (l: %d, c: %d)!\n\n" (lexbuf.lex_curr_p.pos_lnum) (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol)); pyerr_occurred ();


  );;


(****************************)


let set_python_argv argv =
  let py_mod_sys_dict = pymodule_getdict (pyimport_importmodule "sys") in
  let _ = pydict_setitem(py_mod_sys_dict,pystring_fromstring "argv",
			 pytuple_fromarray (Array.map pystring_fromstring argv))
  in ()
;;


let rec read_file fc =
  try
    
    let l = (input_line fc) in
      concat "\n" (l :: (read_file fc) :: [])

  with
    | End_of_file -> ""
;;


let mpython () =
  let mx = pymodule_new "Mymms" in
    
  let sd = pyimport_getmoduledict () in
  let _ = pydict_setitemstring (sd, "Mymms", mx) in
    
  let _ = pydict_setitemstring (pymodule_getdict mx, "pytypecheck", pytypecheck) in
  let _ = pydict_setitemstring (pymodule_getdict mx, "mymms2python", mymms2python) in
  let _ = pydict_setitemstring (pymodule_getdict mx, "simpl", simpl) in
  let _ = pydict_setitemstring (pymodule_getdict mx, "interp", interp) in
  let _ = pydict_setitemstring (pymodule_getdict mx, "simpl2", simpl2) in
  let _ = pydict_setitemstring (pymodule_getdict mx, "interp2", interp2) in
  let _ = pydict_setitemstring (pymodule_getdict mx, "mymmsrequire", mymmsrequire) in
  let _ = pydict_setitemstring (pymodule_getdict mx, "mymmsload", mymmsload) in
  let _ = pydict_setitemstring (pymodule_getdict mx, "addinload", addinload) in
  let _ = pydict_setitemstring (pymodule_getdict mx, "getnormaloutput", getnormaloutput) in
  let _ = pydict_setitemstring (pymodule_getdict mx, "getdebugoutput", getdebugoutput) in
  let _ = pydict_setitemstring (pymodule_getdict mx, "geterroroutput", geterroroutput) in
  let _ = pydict_setitemstring (pymodule_getdict mx, "mymmscommand", mymmscommand) in

    
    try
      
      let filename = Sys.argv.(2) in
      let argv = Array.init ((Array.length Sys.argv) - 2) (fun i -> Sys.argv.(i+2)) in
	set_python_argv argv;
	let filechannel = open_in filename in
	let fl = read_file filechannel in
	let _ =pyrun_simplestring fl in
	  ()
	    
    with
      | Sys_error _ -> print_error "file does not exists\n"; exit 0;
      | Invalid_argument _ -> (	  
	  let _ = pyrun_interactiveloop (0,"-") in      
	    exit 0;
	)
      | e -> raise e
	  
;;
