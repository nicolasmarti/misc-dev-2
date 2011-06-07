open Recv;;
open Random;;
open Connect;;
open Contract;;
open Req;;

(* 
   this should be a "medium" layer in the binding
   allow one to make request, giving handlers (closure) to manage results
*)

module IBTWS: sig 
    
  type t

  val connect: ?addr:string -> ?port:int -> unit -> t  

  val contractDetails: t -> contract -> (msg list -> unit) -> unit

  val recv_and_process: t -> unit

end = struct
    
  module IndexMap = Map.Make(
    struct
      type t = int
      let compare x y = compare x y
    end
  );;


  type t = {
    mutable in_c: in_channel;
    mutable out_c: out_channel;

    (* list of reqIds *)
    mutable ids: int list;

    (* d counter for contractDetails *)
    mutable contractDetailsIds: int;

    (* contract details handler *)
    mutable contractDetailsHandlers: (msg list -> unit) IndexMap.t;

    (* contract details data *)
    mutable contractDetailsData: (msg list) IndexMap.t;

  };;

  let connect ?(addr = "127.0.0.1") ?(port = 7496) () = 
    let clientId = (Random.int 65000) in
    let (ic, oc) = tws_connect addr port clientId in
    {
      in_c = ic;
      out_c = oc;
      ids = [];
      contractDetailsIds = 0;
      contractDetailsHandlers = IndexMap.empty;
      contractDetailsData = IndexMap.empty;
    };;

  let contractDetails data contract handler = 
    let id = data.contractDetailsIds in
    data.contractDetailsIds <- id + 1;
    data.contractDetailsHandlers <- IndexMap.add id handler data.contractDetailsHandlers;
    data.contractDetailsData <- IndexMap.add id [] data.contractDetailsData;
    reqContractDetails id contract data.out_c;;


  let recv_and_process data =
    let msg = processMsg data.in_c in
    match msg with
      (* contractDetails: buffered until end *)
      | ContractData (_, id, _) -> 
	let msgs = IndexMap.find id data.contractDetailsData in
	data.contractDetailsData <- IndexMap.add id (msgs @ [msg]) data.contractDetailsData;
      | BondData (_, id, _) -> 
	let msgs = IndexMap.find id data.contractDetailsData in
	data.contractDetailsData <- IndexMap.add id (msgs @ [msg]) data.contractDetailsData;
      | ContractDataEnd (_, id) ->
	let f = IndexMap.find id data.contractDetailsHandlers in
	let msgs = IndexMap.find id data.contractDetailsData in
	data.contractDetailsHandlers <- IndexMap.remove id data.contractDetailsHandlers;
	data.contractDetailsData <- IndexMap.remove id data.contractDetailsData;
	f msgs
      | _ -> raise (Failure "recv_and_process: msg not yet supported")
;;


end;;
