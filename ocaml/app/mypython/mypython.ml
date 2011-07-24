open Python;;
open Opycaml.Api

let _ =
  Base.initialize ();
  let mdl = Module.new_ "MyModule" in
  let mdldic = Import.getModuleDict () in
  Dict.setItemString mdldic "MyModule" mdl;
  let dic = Module.getDict mdl in
  Dict.setItemString dic "answer" (Int.fromLong 42);
  ignore (Base.main []);
  Base.finalize ()
;;


  
