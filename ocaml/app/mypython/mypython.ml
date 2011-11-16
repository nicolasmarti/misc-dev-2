open Doudou
open Parser
open Lisp;;
open Opycaml.Api;;
open Printf;;
open Pprinter;;

(***************************************************************)

let env = init_ctxt ()

(* transcription of a lisp value into a python value *)
let rec lisp2python (env: env) (expr: expr) : _Object t = 
  match expr with
    | Int i -> Object.obj (Int.fromLong i)
    (*| Float f -> ???*)
    | String s -> Object.obj (Py.String.fromString (String.concat "" ["\""; s; "\""]))
    | SrcInfo (e, _) -> lisp2python env e
    | List [] -> Object.obj (Base.none ())
    | Name n -> (try lisp2python env (Hashtbl.find env n) with | _ -> Object.obj (Py.String.fromString n))
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
    | _ when Py.String.check o -> (
      let s = Py.String.asString (Py.String.coerce o) in
      match () with 
	| _ when String.length s < 2 -> Name s
	| _ when String.sub s 0 1 = "\"" && String.sub s (String.length s - 1) 1 = "\"" -> String s
	| _ -> Name s
    )
    | _ when Int.check o -> Int (Int.asLong (Int.coerce o))
    | _ when Tuple.check o ->
      Quoted (List (List.map python2lisp (Tuple.to_list (Tuple.coerce o))))


let addIfNotIn mdl dict key expr =
  try 
    let _ = Dict.getItemString dict key in
    (*printf "%s found\n" key;*)
    ()
  with
    | _ -> 
      try 
	let _ = Module.addObject mdl key (lisp2python env expr) in
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
  ) env

(***************************************************************)

let defs = ref (empty_defs ())

let ctxt = ref empty_context

let registry : (int, (term * int)) Hashtbl.t = Hashtbl.create 100

let register (te: term) : int =
  let id = Hashtbl.hash te in
  if Hashtbl.mem registry id then
    raise (Failure "id collision ...")
  else
    let s = term2string !ctxt te in
    let _ = Hashtbl.add registry id (te, 1) in
    id  

let marshal_doudou_python createValue te =
  let id = register te in
  let res = Object.call createValue [Object.obj (Int.fromLong id)] in
  res

let marshal_python_doudou valueClass value =
  try
    let isValue = Object.isInstance value valueClass in
    if isValue then
      let id_object = Object.getAttr value (Py.String.fromString "id") in
      let id = Int.asLong (Int.coerce id_object) in
      if not (Hashtbl.mem registry id) then
	None
      else
	let (te, _) = Hashtbl.find registry id in
	Some te        
    else
      None
  with
    | _ -> None

let show_registry () =
  (* iter : ('a -> 'b -> unit) -> ('a, 'b) t -> unit *)
  Hashtbl.iter (fun id (te, rc) ->
    let s = term2string !ctxt te in
    printf "%d: %s\n" id s; flush Pervasives.stdout;    
  ) registry;
    printf "\n\n"; flush Pervasives.stdout

(***************************************************************)

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
	  let consumed, res = interp_expr env str in
	  let consumed = Int.fromLong consumed in
	  let res = lisp2python env res in	
	  let _ = synchModuleCtxt mdl in
	  Object.obj (Tuple.from_list [Object.obj consumed; res])
	)
	| _ -> Object.obj (Base.none ())
    );

  (* importing Lisp module *)
  let _ = Run.simpleString "import Lisp" in

  (********************************************************************)

  (*
    we need a python class that represents Doudou values
    c.f. http://docs.python.org/reference/datamodel.html#basic-customization

  *)

  let _ = Run.simpleString "class Value:
     # just register the id
     # the id should be already registered in ocaml
     def __init__(self, id):
         #print \"python: register \" + str(id) + \": \" + Doudou.to_string(id) 
         #print \"python: registering \" + str(id)
         self.id=id

     # decref the term registered by id
     def __del__(self):
         Doudou.decref(self.id)

     # return the string representation
     def __str__(self):
         return Doudou.to_string(self.id)

     def type(self):
         return Doudou.type(self.id)

     # application (here args is a tuple)
     def __call__(self, *args):
         return Doudou.apply(self.id, args)


def createValue(id):
    return Value(id)



  " in

  (* building Doudou module *)
  let mdl = Module.new_ "Doudou" in
  let mdldic = Import.getModuleDict () in
  Dict.setItemString mdldic "Doudou" mdl;

  let doudou_dict = Module.getDict mdl in

  (* grabing Value *)
  let main_mdl = Import.importModule "__main__" in
  let main_dict = Module.getDict main_mdl in
  let value_class = unsafe_coerce (Dict.getItemString main_dict "Value") in

  let createValue_function = Callable.coerce (Dict.getItemString main_dict "createValue") in

  (* filling the module *)
  (*
    Module.setClosureString : [>_Module] t -> string -> ([>_Tuple] t -> _Object t) -> unit
    Module.setItemString : [>_Module] t -> string -> [>_Object] t -> unit
  *)

  Module.setItemString mdl "Type"
    (marshal_doudou_python value_class (Type nopos));

  (*show_registry ();*)

  (*  *)
  Module.setClosureString mdl "apply"
    (fun args ->
      try(
	let args = Tuple.to_list args in
	match args with
	  | id::args::[] when Number.check id && Tuple.check args -> (
	    let id = Int.asLong (Int.coerce id) in	    
	    if not (Hashtbl.mem registry id) then (
	      Object.obj (Base.none ())
	    )
	    else (
	      let args = Tuple.to_list (Tuple.coerce args) in
	      let rev_args = List.fold_left (fun acc hd -> 
		match acc with
		  | None -> None
		  | Some acc -> 
		    match marshal_python_doudou value_class hd with
		      | None -> None
		      | Some te ->
			Some (te::acc)
	      ) (Some []) args in	      
	      match rev_args with
		| None -> (
		  Object.obj (Base.none ())
		)
		| Some l ->
		  let args = List.rev l in
		  let te = App (
		    fst (Hashtbl.find registry id),
		    List.map (fun hd -> (hd, Explicit)) args,
		    nopos
		  ) in
		  let saved_ctxt = !ctxt in
		  let saved_defs = copy_defs !defs in
		  (*if verbose then printf "input:\n%s\n" str;*)
		  try
		    (* we infer the term type *)
		    let te, ty = typeinfer !defs ctxt te in
		    let te = reduction !defs ctxt clean_term_strat te in
		    let pte = marshal_doudou_python createValue_function te in
		    pte
		  with
		    (* TODO: return proper python exception *)
		    | DoudouException err -> 
		      (* we restore the context and defs *)
		      ctxt := saved_ctxt;
		      defs := saved_defs;
		      Object.obj (Base.none ())
		    | _ -> 
		      Object.obj (Base.none ())
	    )
	  )
	  | _ -> 
	    Object.obj (Base.none ())
      )
      with
	| _ -> 
	  Object.obj (Base.none ())

    );

  Module.setClosureString mdl "to_string"
    (fun args ->
      try(
	let args = Tuple.to_list args in
	match args with
	  | id::[] when Number.check id -> (
	    let id = Int.asLong (Int.coerce id) in	    
	    if not (Hashtbl.mem registry id) then (
	      Object.obj (Base.none ())
	    )
	    else (
	      Object.obj (Py.String.fromString (term2string !ctxt (fst (Hashtbl.find registry id))))
	    )
	    )
	  | _ -> 
	    Object.obj (Base.none ())
      )
      with
	| _ -> 
	  Object.obj (Base.none ())

    );

  Module.setClosureString mdl "decref"
    (fun args ->
      try(
	let args = Tuple.to_list args in
	match args with
	  | id::[] when Number.check id -> (
	    let id = Int.asLong (Int.coerce id) in
	    if not (Hashtbl.mem registry id) then
	      Object.obj (Base.none ())
	    else
	      let (value, refcounter) = Hashtbl.find registry id in
	      let _ = if refcounter = 0 then
		  Hashtbl.remove registry id		    
		else
		  Hashtbl.replace registry id (value, refcounter - 1) in
	      Object.obj (Base.none ())
	    )
	  | _ -> Object.obj (Base.none ())
      )
      with
	| _ -> Object.obj (Base.none ())

    );

  (* enter a doudou definition *)
  Module.setClosureString mdl "proceed"
    (fun args ->
      try(
	let args = Tuple.to_list args in
	match args with
	  | str::_ when Py.String.check str -> (
	    let str = Py.String.asString (Py.String.coerce str) in
	    (* we set the parser *)
	    let lines = stream_of_string str in
	    (* we save the context and the defs *)
	    let saved_ctxt = !ctxt in
	    let saved_defs = copy_defs !defs in
	    (*if verbose then printf "input:\n%s\n" str;*)
	    let pb = build_parserbuffer lines in
	    try
	      let (consumed, def) = parse_onedefinition !defs pb in
	      let symbs = process_definition ~verbose:false defs ctxt def in
	      let o = Object.obj (Base.none ()) in
	      let consumed = Int.fromLong consumed in

	      let _ = List.map (fun symb ->
		let s = (symbol2string symb) in
		(*printf "registering %s\n" s;*)
		let te = Cste (symb, nopos) in
		try 
		  let pte = marshal_doudou_python createValue_function te in
		  Module.setItemString mdl s pte;
		  (*printf "registered %s\n" s*)
		with
		  | _ -> (*printf "failed registerig %s\n" s; flush Pervasives.stdout;*) ()
	      ) symbs in
	
	      Object.obj (Tuple.from_list [Object.obj consumed; o])	    
	    with
	      (* TODO: return proper python exception *)
	      | NoMatch -> 
		printf "parsing error: '%s'\n%s\n" (Buffer.contents pb.bufferstr) (errors2string pb);
		Object.obj (Py.String.fromString (errors2string pb))
	      | DoudouException err -> 
	      (* we restore the context and defs *)
		ctxt := saved_ctxt;
		defs := saved_defs;
		printf "error:\n%s\n" (error2string err); flush Pervasives.stdout;
		Object.obj (Py.String.fromString (error2string err))
	  )
	  | _ -> Object.obj (Base.none ())
      )
      with
	| _ -> Object.obj (Base.none ())

    );

  (* undo last definition *)
  Module.setClosureString mdl "undo"
    (fun args ->
      try 
	let symbs = undoDefinition defs in
	let _ = List.map (fun symb ->
	  let s = symbol2string symb in
	  try 
	    Dict.delItemString doudou_dict s
	  with
	    | _ -> (*printf "failed unregisterig %s\n" s; flush Pervasives.stdout;*) ()
	) symbs in
	Object.obj (Base.none ())
      with
	| DoudouException err -> 
	  (* we restore the context and defs *)
	  printf "error:\n%s\n" (error2string err); flush Pervasives.stdout;
	  Object.obj (Py.String.fromString (error2string err))
    );

  (* show definitions *)
  Module.setClosureString mdl "showdefs"
    (fun args ->
      let s = defs2string !defs in
      Object.obj (Py.String.fromString s)
    );


  (* importing Lisp module *)
  let _ = Run.simpleString "import Doudou" in

  (********************************************************************)

  (* running the shell *)
  ignore (Base.main []);
  Base.finalize ()
;;


  
