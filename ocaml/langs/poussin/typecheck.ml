open Datastructures

(* this is the whole set of functions needed for typechecking, it includes,
   - reduction
   - unification
   - typeinference
   - typechecking
*)

let rec reduction (ctxt: context ref) (strat: reduction_strategy) (te: term) : term = 
  raise (Failure "NYI")
and unification (ctxt: context ref) (te1: term) (te2: term) : term =
  raise (Failure "NYI")
and typecheck (ctxt: context ref) (te: term) (ty: term) : term * term =
  raise (Failure "NYI")
and typeinfer (ctxt: context ref) (te: term) : term * term =
  raise (Failure "NYI")
