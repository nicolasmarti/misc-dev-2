open Opycaml.Api
open Lang_intf;;
open Type;;

(*
  not sure that's really usefull ...
*)

module PythonLang : Lang =
struct
  type value = _Object t
  type ltype = _Type t
  type session = string

  type error = string

  exception Exception of error

  let error2string = fun _ -> "Not Yet Implemented"

  let name = "Python"

  let empty_session () = "new_session"

  let proceed session expr = 
    let _ = Run.simpleString expr in
    (0, Object.obj (Base.none ()))

  let proceeds session exprs = 
    let _ = Run.simpleString exprs in
    (0, [])

  let print session value = 
    Object.str_string value

  let get_type session value = raise (Failure "NYI")

  let lookup session name = raise (Failure "NYI")

  let get_defs session = raise (Failure "NYI")

  let apply session fct args = 
    Object.callObject (unsafe_coerce fct) (List.map unsafe_coerce args)

end;;
