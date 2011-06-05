open Unix;;
open Encdec;;
open Pervasives;;
open Contract;;
open Printf;;
open Scannersubscription;;

let tick_price = 1;;
let tick_size = 2;;
let order_status = 3;;
let err_msg = 4;;
let open_order = 5;;
let acct_value = 6;;
let portfolio_value = 7;;
let acct_update_time = 8;;
let next_valid_id = 9;;
let contract_data = 10;;
let execution_data = 11;;
let market_depth = 12;;
let market_depth_l2 = 13;;
let news_bulletins = 14;;
let managed_accts = 15;;
let receive_fa = 16;;
let historival_data = 17;;
let bond_contract_data = 18;;
let scanner_parameters = 19;;
let scanner_data = 20;;
let tick_option_computation = 21;;
let tick_generic = 45;;
let tick_string = 46;;
let tick_efp = 47;;
let current_time = 49;;
let real_time_bars = 50;;
let fundamental_data = 51;;
let contract_data_end = 52;;
let open_order_end = 53;;
let acct_download_end = 54;;
let execution_data_end = 55;;
let delta_netural_validation = 56;;
let tick_snapshot_end = 57;;

let currId = ref 0;;    

type bardata = {
  mutable date: string;
  mutable bopen: float;
  mutable high: float;
  mutable low: float;
  mutable close: float;
  mutable volume: int;
  mutable average: float;
  mutable hasGaps: string;
  mutable barCount: int;
};;

let mkbardata () = {
  date = "";
  bopen = 0.0;
  high = 0.0;
  low = 0.0;
  close = 0.0;
  volume = 0;
  average = 0.0;
  hasGaps = "";
  barCount = 0;
};;

(* EClientSocketBase::processMsg *)

let processMsg (ic: in_channel) : unit =
  let msgId = decode_int ic in
    match msgId with
      | 4 (*err_msg*) -> (
	  let version = decode_int ic in
	  let id = decode_int ic in
	  let errCode = decode_int ic in
	  let errMsg = decode_string ic in
	    printf "error msg (%d): %s\n\n" errCode errMsg
	)
      | 1 (*tick_price*) -> (
	  let version = decode_int ic in
	  let tickerId = decode_int ic in
	  let tickTypeInt = decode_int ic in
	  let price = decode_float ic in
	  let size = decode_int ic in
	  let canAutoExecute = decode_int ic in
	    printf "TickPrice: (%d, %d, %d, %f, %d, %d)\n\n" version tickerId tickTypeInt price size canAutoExecute
	)
      | 2 (*tick_size*) -> (
	  let version = decode_int ic in
	  let tickerId = decode_int ic in
	  let tickTypeInt = decode_int ic in
	  let size = decode_int ic in
	    printf "TickSize: (%d, %d, %d, %d)\n\n" version tickerId tickTypeInt size
	)
      | 9 (*next_valid_id*) -> (
	  let version = decode_int ic in
	  let orderId = decode_int ic in
	    currId := orderId;
	    printf "next orderId: %d\n\n" orderId
	)
      | 53 (*open_order_end*) -> (
	  let version = decode_int ic in
	    printf "open order end: %d\n\n" version
	)
      | 46 (*tick_string *) -> (
	  let version = decode_int ic in
	  let tickerId = decode_int ic in
	  let tickTypeInt = decode_int ic in
	  let value = decode_string ic in
	    printf "TickString: (%d, %d, %d, %s)\n\n" version tickerId tickTypeInt value
	)
      | 45 (* tick_generic *) -> (
	  let version = decode_int ic in
	  let tickerId = decode_int ic in
	  let tickTypeInt = decode_int ic in
	  let value = decode_float ic in
	    printf "TickString: (%d, %d, %d, %f)\n\n" version tickerId tickTypeInt value

	)
      | 57 (* tick_snapshot_end *) -> (
	  let version = decode_int ic in
	  let reqId = decode_int ic in
	    printf "TickSnapshotEnd: (%d, %d)\n\n" version reqId
	)

      | 12 (* market_depth *) -> (
	  let version = decode_int ic in
	  let id = decode_int ic in
	  let position = decode_int ic in
	  let operation = decode_int ic in
	  let side = decode_int ic in
	  let price = decode_float ic in
	  let size = decode_int ic in
	    printf "MarketDepth (%d, %d, %d, %d, %d, %g, %d)\n\n" version id position operation side price size
	)
      | 13 (* market_depth_l2 *) -> (
	  let version = decode_int ic in
	  let id = decode_int ic in
	  let position = decode_int ic in
	  let marketMaker = decode_string ic in
	  let operation = decode_int ic in
	  let side = decode_int ic in
	  let price = decode_float ic in
	  let size = decode_int ic in
	    printf "MarketDepth l2 (%d, %d, %d, %s, %d, %d, %g, %d)\n\n" version id position marketMaker operation side price size
	)
      | 17 (* historical_data *) -> (
	  let version = decode_int ic in
	  let reqId = decode_int ic in
	  let startDateStr = decode_string ic in
	  let endDateStr = decode_string ic in
	    printf "Historical data (%d, %d, %s, %s)\n" version reqId startDateStr endDateStr;
	    let itemCount = ref (decode_int ic) in
	      while !itemCount > 0 do
		let date = decode_string ic in
		let bopen = decode_float ic in
		let high = decode_float ic in
		let low = decode_float ic in
		let close = decode_float ic in
		let volume = decode_int ic in
		let average = decode_float ic in
		let hasGaps = decode_string ic in
		let barCount = decode_int ic in
		  printf "HistoricalData(%s, %f, %f, %f, %f, %d, %f, %s, %d)\n" date bopen high low close volume average hasGaps barCount;
		  itemCount := !itemCount - 1;
	      done;	    

	)
      | 50 (* real_time_bars *) -> (
	  let version = decode_int ic in
	  let reqId = decode_int ic in
	  let time = decode_int ic in

	  let bopen = decode_float ic in
	  let high = decode_float ic in
	  let low = decode_float ic in
	  let close = decode_float ic in
	  let volume = decode_int ic in
	  let average = decode_float ic in
	  let count = decode_int ic in
	    
	  printf "REALTIMEBAR(%d, %d, %d, %f, %f, %f, %f, %d, %f, %d)\n" version reqId time bopen high low close volume average count;
      )
      | 19 (* scanner_parameters *) -> (
	let version = decode_int ic in
	let xml = decode_string ic in
	printf "SCANNERPARAMETER(%d, %s)" version xml;
      )	  
      | 20 (* scanner_data *) -> (
	  let version = decode_int ic in
	  let reqId = decode_int ic in
	  let numberOfElements = decode_int ic in
	  let res = Array.init numberOfElements (fun _ -> build_scanData ()) in
	  let index = ref 0 in
	  while !index < numberOfElements do 
	    res.(!index).rank <- decode_int ic;
	    res.(!index).con.summary.conId <- decode_int ic;
	    res.(!index).con.summary.symbol <- decode_string ic;
	    res.(!index).con.summary.secType <- decode_string ic;
	    res.(!index).con.summary.expiry <- decode_string ic;
	    res.(!index).con.summary.strike <- decode_float ic;
	    res.(!index).con.summary.right <- decode_string ic;
	    res.(!index).con.summary.exchange <- decode_string ic;
	    res.(!index).con.summary.currency <- decode_string ic;
	    res.(!index).con.summary.localSymbol <- decode_string ic;
	    res.(!index).con.marketName <- decode_string ic;
	    res.(!index).con.tradingClass <- decode_string ic;
	    res.(!index).distance <- decode_string ic;
	    res.(!index).benchmark <- decode_string ic;
	    res.(!index).projection <- decode_string ic;
	    res.(!index).legsStr <- decode_string ic;
	    index := !index + 1;
	  done
      )
      | id -> (
	printf "%s\n" (String.concat " " ["not yet supported:";(string_of_int id)]);
	raise (Failure (String.concat " " ["not yet supported:";(string_of_int id)]))
      )
;;

(*
  next:
  EClientSocketBase::reqFundamentalData
  l. 908
*)

