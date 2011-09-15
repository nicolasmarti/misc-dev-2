open Lisp;;
open Opycaml.Api;;
open Printf;;
open Pprinter;;

let ctxt = init_ctxt ()

(* transcription of a lisp value into a python value *)
let rec lisp2python (env: env) (expr: expr) : _Object t = 
  match expr with
    | Int i -> Object.obj (Int.fromLong i)
    (*| Float f -> ???*)
    | String s -> Object.obj (Py.String.fromString s)
    | SrcInfo (e, _) -> lisp2python env e
    | List [] -> Object.obj (Base.none ())
    | Name n -> lisp2python env (Hashtbl.find env n)
    | Obj o when o#uuid = 1 ->
      Object.obj (Base.embed_closure (fun args ->
	let args = Tuple.to_list args in
	let args = List.map python2lisp args in
	let res = 
	  try 
	    eval (List (expr::args)) env
	  with
	    | LispException err ->
	      printf "%s\n" (box2string (token2box (execException2box err) 400 2)); flush Pervasives.stdout;
	      List []
	in
	(*printbox (token2box (expr2token res) 400 2);*)
	lisp2python env res
      ))
    | List l ->
      Object.obj (Tuple.from_list (List.map (lisp2python env) l))
      
and python2lisp (o: _Object t) : expr =
  match () with
    | _ when Py.String.check o -> String (Py.String.asString (Py.String.coerce o))
    | _ when Int.check o -> Int (Int.asLong (Int.coerce o))
    | _ when Tuple.check o ->
      List (List.map python2lisp (Tuple.to_list (Tuple.coerce o)))


let addIfNotIn mdl dict key expr =
  try 
    let _ = Dict.getItemString dict key in
    (*printf "%s found\n" key;*)
    ()
  with
    | _ -> 
      try 
	let _ = Module.addObject mdl key (lisp2python ctxt expr) in
	(*printf "%s added\n" key;*)
	()
      with
	| _ -> 
	  (*printf "adding %s failed\n" key;*)
	  ()

let synchModuleCtxt mdl =
  let dict = Module.getDict mdl in
  Hashtbl.iter (fun key expr ->
    match expr with
      | Obj o when o#uuid = 1 -> addIfNotIn mdl dict key expr
      | Obj o -> ()
      | _ -> addIfNotIn mdl dict key expr
  ) ctxt


let _ =
  (* initialization *)
  Base.initialize ();

  (********************************************************************)

  (* building Lisp module *)
  let mdl = Module.new_ "Lisp" in
  let mdldic = Import.getModuleDict () in
  Dict.setItemString mdldic "Lisp" mdl;

  (* filling the module *)
  (*
    Module.setClosureString : [>_Module] t -> string -> ([>_Tuple] t -> _Object t) -> unit
    Module.setItemString : [>_Module] t -> string -> [>_Object] t -> unit
  *)

  (* define a test *)
  Module.setClosureString mdl "test"
    (fun args ->
      let args = Tuple.to_list args in
      let res = List.map (fun v -> Object.str_string (Object.obj v)) args in      
      let res = Tuple.from_list (List.map (Py.String.fromString) res) in      
      Object.obj res);

  Module.setClosureString mdl "test2"
    (fun args ->
      let args = Tuple.to_list args in
      let res = List.map (fun v -> Object.str_string (Object.type_ v)) args in      
      let res = Tuple.from_list (List.map (Py.String.fromString) res) in      
      Object.obj res);


  (* enter a lisp value *)
  Module.setClosureString mdl "proceed"
    (fun args ->
      let args = Tuple.to_list args in
      match args with
	| str::_ when Py.String.check str -> (
	  let str = Py.String.asString (Py.String.coerce str) in
	  let consumed, res = interp_expr ctxt str in
	  let consumed = Int.fromLong consumed in
	  let res = lisp2python ctxt res in	
	  let _ = synchModuleCtxt mdl in
	  Object.obj (Tuple.from_list [Object.obj consumed; res])
	)
	| _ -> Object.obj (Base.none ())
    );



  (* importing Lisp module *)
  let _ = Run.simpleString "import Lisp" in

  (********************************************************************)

  (* running the shell *)
  ignore (Base.main []);
  Base.finalize ()
;;


  
