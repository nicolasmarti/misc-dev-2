open Lisp;;
open Opycaml.Api;;
open Printf;;

let session = LispLang.empty_session ();;

let _ =
  (* initialization *)
  Base.initialize ();

  (* building Lisp module *)
  let mdl = Module.new_ "Lisp" in
  let mdldic = Import.getModuleDict () in
  Dict.setItemString mdldic "Lisp" mdl;

  (* filling the module *)
  (*
    Module.setClosureString : [>_Module] t -> string -> ([>_Tuple] t -> _Object t) -> unit
    Module.setItemString : [>_Module] t -> string -> [>_Object] t -> unit
  *)

  (* define a term *)
  Module.setClosureString mdl "proceed"
    (fun args ->
      let args = Tuple.to_list args in
      let res = List.map (fun v -> Object.str_string (Object.obj v)) args in      
      let res = Tuple.from_list (List.map (Py.String.fromString) res) in      
      Object.obj res);

  (* define terms *)
  Module.setClosureString mdl "proceeds"
    (fun args -> Object.obj (Base.none ()));

  (* importing Lisp module *)
  let _ = Run.simpleString "import Lisp" in

  (* running the shell *)
  ignore (Base.main []);
  Base.finalize ()
;;


  
