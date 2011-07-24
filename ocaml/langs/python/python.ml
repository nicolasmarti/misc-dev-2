open Opycaml.Api
open Lang_intf;;
open Type;;

module PythonLang : Lang =
struct
  type value = _Object t
  type ltype = _Type t
  type session = unit

  type error = PythonException of string

  exception Exception of error

  let error2string = fun _ -> "Not Yet Implemented"

  let name = "Python"

  let empty_session () = ()

  let proceed session expr = raise (Failure "NYI")

  let proceeds session exprs = raise (Failure "NYI")

  let print session value = raise (Failure "NYI")

  let get_type session value = raise (Failure "NYI")

  let lookup session name = raise (Failure "NYI")

  let get_defs session = raise (Failure "NYI")

  let apply session fct args = raise (Failure "NYI")

end;;
