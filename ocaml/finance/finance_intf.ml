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
		  | Cancelled
		  | Pending

  val proceedOrder: t -> order -> orderId
  val orderStatus: t -> orderId -> orderRes
  val cancelOrder: t -> orderId -> unit
  val closeOrder: t -> orderId -> orderId

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
  type order

  (* the start parameters (code, ...) *)
  type t

  type signal = GOLONG of order
		| GOSHORT of order
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
    functor (S: Strat with type data = B.data and type info = B.info and type order = B.order) ->
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
      if B.getstatus self.broker == B.STOPPED then self.st <- STOPPED else
	match self.st with
	  | CLOSED -> (
	    let d = B.getdata self.broker in
	    let s = S.proceedData self.strat d in
	    match s with
	      | S.STAY | S.CLOSE -> ()
	      | S.GOLONG o | S.GOSHORT o -> 
		let oid = B.proceedOrder self.broker o in
		let dt = now () in
		self.st <- OPENING (oid, dt)		
	  )
	  | OPENING (o, dt) -> (
	    let n = now () in
	    let delta = diff_datetime n dt in	    
	    match B.orderStatus self.broker o with
	      | B.Filled -> self.st <- OPENED o
	      | B.Pending -> if (match delta with
		  | Second s -> s > 5
		  | Day d -> d > 0
		  | Week w -> w > 0
	      ) then B.cancelOrder self.broker o else ()
	      | B.Cancelled -> self.st <- OPENED o	      
	  )
	  | OPENED o -> (
	    let d = B.getdata self.broker in
	    let s = S.proceedData self.strat d in
	    match s with
	      | S.STAY -> ()
	      | S.GOLONG o | S.GOSHORT o -> raise (Failure "???")
	      | S.CLOSE -> 	    
		    let oid = B.closeOrder self.broker o in
		    let dt = now () in
		    self.st <- OPENING (oid, dt)
	  )
	  | CLOSING (o, dt) -> (
	    match B.orderStatus self.broker o with
	      | B.Filled -> self.st <- CLOSED
	      | B.Pending -> ()
	      | B.Cancelled -> raise (Failure "???")
	  )
	  | STOPPED -> (
	    raise (Failure "Impossible state at this stage")
	  )
  ;;
	    
  let get_status (self: t) : status =
    self.st;;

  let init (strat: S.t) = 
    {
      strat = strat;
      broker = B.init (S.getinfo strat);
      st = STOPPED;
    }

end;; 


