(*
  a broker:
  - ibtws
  - yahoo/google
*)
module type Broker = sig

  (* describe the entity manipulated by the module *)
  type t

  (* the data that Broker provide (feeds, order states, ...) *)
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

  val orderValue: t -> orderId -> float
  val orderPnL: t -> orderId -> float

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

  type status = LONG
		| SHORT
		| CLOSED

  val getinfo: t -> info
  val proceedData: t -> data -> signal
  val setstatus: t -> status -> unit
    
end;;


(*
  an automata 
*)
open Date;;
open Printf;;


module Automata =
  functor (B: Broker) ->
    functor (S: Strat with type data = B.data and type info = B.info and type order = B.order) ->
struct
  
  type status = CLOSED
		| OPENING of B.orderId * datetime * [`LONG | `SHORT]
		| OPENED of B.orderId 
		| CLOSING of B.orderId * B.orderId * datetime
		| STOPPED

  type t = {
    strat: S.t;
    broker: B.t;
    mutable st: status;
    mutable pnl: float;
    mutable maxpos: float;
    mutable opendays: int;
  };;

  let step self debug =
    if self.st == STOPPED then (if debug then printf "is STOPPED\n") else      
      if B.getstatus self.broker == B.STOPPED then (self.st <- STOPPED; (if debug then printf "? -> STOPPED\n")) else
	match self.st with
	  | CLOSED -> (
	    if debug then printf "CLOSED\n";
	    let d = B.getdata self.broker in
	    let s = S.proceedData self.strat d in
	    match s with
	      | S.STAY | S.CLOSE -> ()
	      | S.GOLONG o | S.GOSHORT o -> 
		let oid = B.proceedOrder self.broker o in
		let dt = now () in
		self.st <- OPENING (oid, dt, match s with | S.GOLONG _ -> `LONG | S.GOSHORT _ -> `SHORT);
		if debug then printf "CLOSED -> OPENING(%s)\n" (match s with | S.GOLONG _ -> "LONG" | S.GOSHORT _ -> "SHORT")
	  )
	  | OPENING (o, dt, dir) -> (
	    if debug then printf "OPENING\n";
	    let n = now () in
	    let delta = diff_datetime n dt in	    
	    match B.orderStatus self.broker o with
	      | B.Cancelled -> self.st <- CLOSED
	      | B.Pending -> if (match delta with
		  | Second s -> s > 5
		  | Day d -> d > 0
		  | Week w -> w > 0
	      ) then B.cancelOrder self.broker o else ()
	      | B.Filled -> 
		self.st <- OPENED o; 
		S.setstatus self.strat (match dir with | `LONG -> S.LONG | `SHORT -> S.SHORT);
		if debug then printf "OPENING -> OPENED(%s)\n" (match dir with | `LONG -> "LONG" | `SHORT -> "SHORT");
		let value = B.orderValue self.broker o in
		if self.maxpos < value then self.maxpos <- value
	  )
	  | OPENED o -> (
	    if debug then printf "OPENED\n";
	    let d = B.getdata self.broker in
	    let s = S.proceedData self.strat d in
	    self.opendays <- self.opendays + 1;
	    match s with
	      | S.STAY -> ()
	      | S.GOLONG o | S.GOSHORT o -> raise (Failure "???")
	      | S.CLOSE -> 	    
		    let oid = B.closeOrder self.broker o in
		    let dt = now () in
		    self.st <- CLOSING (o, oid, dt);
		    if debug then printf "OPENED -> CLOSING\n"
	  )
	  | CLOSING (o1 , o2, dt) -> (
	    if debug then printf "CLOSING\n";
	    match B.orderStatus self.broker o2 with
	      | B.Filled -> 
		self.st <- CLOSED; 
		S.setstatus self.strat S.CLOSED; 
		let pnl = B.orderPnL self.broker o1 in
		if debug then printf "CLOSING -> CLOSED (PnL = %f)\n" pnl;
		self.pnl <- self.pnl +. pnl
	      | B.Pending -> ()
	      | B.Cancelled -> raise (Failure "???")
	  )
	  | STOPPED -> (
	    raise (Failure "Impossible state at this stage")
	  )
  ;;
	    
  let getstatus (self: t) : status =
    self.st;;

  let init (strat: S.t) = 
    {
      strat = strat;
      broker = B.init (S.getinfo strat);
      st = STOPPED;
      pnl = 0.0;
      maxpos = 0.0;
      opendays = 0;
    }

  let start self =
    B.start self.broker;
    self.st <- CLOSED;;

  let getpnl self = self.pnl;;

  let getmaxpos self = self.maxpos;;

  let getopendays self = self.opendays;;

end;; 


