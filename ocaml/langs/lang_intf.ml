module NameMap = Map.Make(
  struct
    type t = string
    let compare x y = compare x y
  end
);;

(*
  This interface is meant to capture
  a languages, with session, values, types, ...
  Should allow to build a functor for embedded in python module
*)

module type Lang = sig
    
  type value    
  type ltype
  type session    

  val name: string

  (* generate an empty session *)
  val empty_session: unit -> session

  (* parse/typecheck/compile/... an expression, and register it in the session *)
  val proceed: session -> string -> value
    
  (* return the type of a value *)
  val get_type: session -> value -> ltype

  (* retrieve a value by name *) 
  val lookup: session -> string -> value

  (* returns the set of defined names in a session *)
  val get_defs: session -> ltype NameMap.t

end;;

