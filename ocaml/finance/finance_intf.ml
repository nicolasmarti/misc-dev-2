(*
  a broker
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

  val getdata: t -> data
  val start: info -> t
  val stop: t -> unit
  val getstatus: t -> status

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
  a strategy 
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

  val init: t -> info
  val proceedData: t -> data -> signal
    
end;;


(*
  an automata 
*)
open Data;;

module type Automata = 
  functor (B: Broker) ->
    functor (S: Strat with type data = Broker.data and type state = Broker.state) ->
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

  val step: t -> unit

  val get_status: t -> status

  val init: S.t -> B.t -> t

end;;

