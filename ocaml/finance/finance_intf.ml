(*
  a broker:
  - ibtws
  - yahoo/google
*)
module type Broker = sig

  (* describe the entity manipulated by the module *)
  type t

  (* the data that Broker agregate (feeds, order states, ...) *)
  type data    

  (* the info contains:
     - the data needed from the broker
  *) 
  type info

  (* the status *)
  type status = RUNNING
		| STOPPED

    
  val init: info -> t    
  val start: t -> unit
  val stop: t -> unit
  val getstatus: t -> status
  val getdata: t -> data

  (* the data for the order *)
  type order

  (* the unique id for orders *)
  type orderId

  type orderRes = Filled
		  | NotFilled
		  | Cancelled
		  | Pending

  val proceedOrder: t -> order -> orderId
  val orderStatus: t -> orderId -> orderRes
  val cancelOrder: t -> orderId -> orderRes

end;;

(*
  a strategy:
  - ideally should be derived from a dsl
*)
module type Strat = sig

  (* the info contains the data needed *)
  type info

  (* the data received from the broker to make a decision *) 
  type data

  (* the start parameters (code, ...) *)
  type t

  type signal = GOLONG
		| GOSHORT
		| CLOSE
		| STAY

  val getinfo: t -> info
  val proceedData: t -> data -> signal
    
end;;


(*
  an automata 
*)
open Date;;

module Automata =
  functor (B: Broker) ->
    functor (S: Strat with type data = B.data and type info = B.info) ->
struct
  
  type status = CLOSED
		| OPENING of B.orderId * datetime
		| OPENED of B.orderId
		| CLOSING of B.orderId * datetime
		| STOPPED

  type t = {
    strat: S.t;
    broker: B.t;
    mutable st: status;
  };;

  let step self =
    if self.st == STOPPED then () else
      match self.st with
	| CLOSED -> (
	  	  raise (Failure "NYI")
	)
	| CLOSED -> (
	  raise (Failure "NYI")
	)
	| CLOSED -> (
	  raise (Failure "NYI")
	)
	| CLOSED -> (
	  raise (Failure "NYI")
	)
	| STOPPED -> (
	  raise (Failure "Impossible state at this stage")
	)

  let get_status (self: t) : status =
    self.st;;

  let init (strat: S.t) = 
    {
      strat = strat;
      broker = B.init (S.getinfo strat);
      st = STOPPED;
    }

end;; 


