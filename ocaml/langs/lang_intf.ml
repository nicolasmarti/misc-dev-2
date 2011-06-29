(*
  This interface is meant to capture
  a languages, with session, values, types, ...
  Should allow to build a functor for embedded in python module
*)

module type Lang = sig
    
  type value    
  type ltype
  type session    

  (* identifier of the language, should be unique *)
  val name: string

  (* generate an empty session *)
  val empty_session: unit -> session

  (* parse/typecheck/compile/... an expression, and register it in the session *)
  val proceed: session -> string -> value
    
  (* pretty printing of values *)
  val print: session -> value -> string

  (* return the type of a value *)
  val get_type: session -> value -> ltype

  (* retrieve a value by name *) 
  val lookup: session -> string -> value

  (* returns the set of defined names in a session *)
  val get_defs: session -> (string * ltype) list

  (* the main features of language: application *)
  val apply: session -> value -> value list -> value

end;;

(*
  general compilation/translation interface

  might allow:
  * to compile a language to llvm
  * interface a language with python
  
*)
module type Compiler = 
  functor (Target: Lang) ->
    functor (Source: Lang) ->
      sig 
	(* session mapping *)
	val sessionmap: Source.session -> Target.session

	(* type mapping *)
	val typemap: Source.session -> Source.ltype -> Target.ltype

	(* value mapping *)
	val valuemap: Source.session -> Source.value -> Target.value

	(* value mapping inverse *)
	val valuerevmap: Source.session -> Source.ltype -> Target.value -> Source.value
      end;;

(* 

module type Prout =
  functor(L1: Lang) -> 
    functor (L2: Lang with type t = L1.ltype) ->


module type Compilable :
  functor (L : Lang with type value = int) ->
    sig
      val compile: L.value -> unit
    end;;

module L: sig Lang end = struct ... end
    

module M: P(Lang with type ... ) with type .... = struct .. end

module F(X : sig ... end) = struct ... end


let x = F(Z).z

*)
