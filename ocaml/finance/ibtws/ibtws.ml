open Recv;;
open Random;;
open Connect;;
open Contract;;
open Req;;

(* 
   this should be a "medium" layer in the binding
   allow one to make request, giving handlers (closure) to manage results
*)

open Unix;;

type genericTickType = OptVol
		       | OptOpenInt
		       | HistVol
		       | OptImpliedVol
		       | IndFutPremium
		       | MiscStat
		       | AuctionVal
		       | RTVol
		       | Shortage
		       | Inventory
		       | FundRatio
		       | RTHistVol
;;

let genericTickType2Int (t: genericTickType) : int =
  match t with
    | OptVol -> 100
    | OptOpenInt -> 101
    | HistVol -> 104
    | OptImpliedVol -> 106
    | IndFutPremium -> 162
    | MiscStat -> 165
    | AuctionVal -> 221
    | RTVol -> 225
    | Shortage -> 233
    | Inventory -> 256
    | FundRatio -> 258
    | RTHistVol -> 411
;;

type tickType = BID_SIZE
		| BID_PRICE
		| ASK_PRICE
		| ASK_SIZE
		| LAST_PRICE
		| LAST_SIZE
		| HIGH
		| LOW
		| VOLUME
		| CLOSE_PRICE
		| BID_OPTION_COMPUTATION
		| ASK_OPTION_COMPUTATION
		| LAST_OPTION_COMPUTATION
		| MODEL_OPTION_COMPUTATION
		| OPEN_TICK
		| LOW_13_WEEK
		| HIGH_13_WEEK
		| LOW_26_WEEK
		| HIGH_26_WEEK
		| LOW_52_WEEK
		| HIGH_52_WEEK
		| AVG_VOLUME
		| OPEN_INTEREST
		| OPTION_HISTORICAL_VOL
		| OPTION_IMPLIED_VOL
		| OPTION_BID_EXCH
		| OPTION_ASK_EXCH
		| OPTION_CALL_OPEN_INTEREST
		| OPTION_PUT_OPEN_INTEREST
		| OPTION_CALL_VOLUME
		| OPTION_PUT_VOLUME
		| INDEX_FUTURE_PREMIUM
		| BID_EXCH
		| ASK_EXCH
		| AUCTION_VOLUME
		| AUCTION_PRICE
		| AUCTION_IMBALANCE
		| MARK_PRICE
		| BID_EFP_COMPUTATION
		| ASK_EFP_COMPUTATION
		| LAST_EFP_COMPUTATION
		| OPEN_EFP_COMPUTATION
		| HIGH_EFP_COMPUTATION
		| LOW_EFP_COMPUTATION
		| CLOSE_EFP_COMPUTATION
		| LAST_TIMESTAMP
		| SHORTABLE
		| FUNDAMENTAL_RATIOS
		| RT_VOLUME
		| HALTED
		| BIDYIELD
		| ASKYIELD
		| LASTYIELD
		| CUST_OPTION_COMPUTATION
		| TRADE_COUNT
		| TRADE_RATE
		| VOLUME_RATE
;;

let tickType2Int (t: tickType) : int =
  match t with
    | BID_SIZE -> 0
    | BID_PRICE -> 1
    | ASK_PRICE -> 2
    | ASK_SIZE -> 3
    | LAST_PRICE -> 4
    | LAST_SIZE -> 5
    | HIGH -> 6
    | LOW -> 7
    | VOLUME -> 8
    | CLOSE_PRICE -> 9
    | BID_OPTION_COMPUTATION -> 10
    | ASK_OPTION_COMPUTATION -> 11
    | LAST_OPTION_COMPUTATION -> 12
    | MODEL_OPTION_COMPUTATION -> 13
    | OPEN_TICK -> 14
    | LOW_13_WEEK -> 15
    | HIGH_13_WEEK -> 16
    | LOW_26_WEEK -> 17
    | HIGH_26_WEEK -> 18
    | LOW_52_WEEK -> 19
    | HIGH_52_WEEK -> 20
    | AVG_VOLUME -> 21
    | OPEN_INTEREST -> 22
    | OPTION_HISTORICAL_VOL -> 23
    | OPTION_IMPLIED_VOL -> 24
    | OPTION_BID_EXCH -> 25
    | OPTION_ASK_EXCH -> 26
    | OPTION_CALL_OPEN_INTEREST -> 27
    | OPTION_PUT_OPEN_INTEREST -> 28
    | OPTION_CALL_VOLUME -> 29
    | OPTION_PUT_VOLUME -> 30
    | INDEX_FUTURE_PREMIUM -> 31
    | BID_EXCH -> 32
    | ASK_EXCH -> 33
    | AUCTION_VOLUME -> 34
    | AUCTION_PRICE -> 35
    | AUCTION_IMBALANCE -> 36
    | MARK_PRICE -> 37
    | BID_EFP_COMPUTATION -> 38
    | ASK_EFP_COMPUTATION -> 39
    | LAST_EFP_COMPUTATION -> 40
    | OPEN_EFP_COMPUTATION -> 41
    | HIGH_EFP_COMPUTATION -> 42
    | LOW_EFP_COMPUTATION -> 43
    | CLOSE_EFP_COMPUTATION -> 44
    | LAST_TIMESTAMP -> 45
    | SHORTABLE -> 46
    | FUNDAMENTAL_RATIOS -> 47
    | RT_VOLUME -> 48
    | HALTED -> 49
    | BIDYIELD -> 50
    | ASKYIELD -> 51
    | LASTYIELD -> 52
    | CUST_OPTION_COMPUTATION -> 53
    | TRADE_COUNT -> 54
    | TRADE_RATE -> 55
    | VOLUME_RATE -> 56
;;

let tickTypeFromInt (i: int) : tickType =
  match i with
    | 0 -> BID_SIZE
    | 1 -> BID_PRICE
    | 2 -> ASK_PRICE
    | 3 -> ASK_SIZE
    | 4 -> LAST_PRICE
    | 5 -> LAST_SIZE
    | 6 -> HIGH
    | 7 -> LOW
    | 8 -> VOLUME
    | 9 -> CLOSE_PRICE
    | 10 -> BID_OPTION_COMPUTATION
    | 11 -> ASK_OPTION_COMPUTATION
    | 12 -> LAST_OPTION_COMPUTATION
    | 13 -> MODEL_OPTION_COMPUTATION
    | 14 -> OPEN_TICK
    | 15 -> LOW_13_WEEK
    | 16 -> HIGH_13_WEEK
    | 17 -> LOW_26_WEEK
    | 18 -> HIGH_26_WEEK
    | 19 -> LOW_52_WEEK
    | 20 -> HIGH_52_WEEK
    | 21 -> AVG_VOLUME
    | 22 -> OPEN_INTEREST
    | 23 -> OPTION_HISTORICAL_VOL
    | 24 -> OPTION_IMPLIED_VOL
    | 25 -> OPTION_BID_EXCH
    | 26 -> OPTION_ASK_EXCH
    | 27 -> OPTION_CALL_OPEN_INTEREST
    | 28 -> OPTION_PUT_OPEN_INTEREST
    | 29 -> OPTION_CALL_VOLUME
    | 30 -> OPTION_PUT_VOLUME
    | 31 -> INDEX_FUTURE_PREMIUM
    | 32 -> BID_EXCH
    | 33 -> ASK_EXCH
    | 34 -> AUCTION_VOLUME
    | 35 -> AUCTION_PRICE
    | 36 -> AUCTION_IMBALANCE
    | 37 -> MARK_PRICE
    | 38 -> BID_EFP_COMPUTATION
    | 39 -> ASK_EFP_COMPUTATION
    | 40 -> LAST_EFP_COMPUTATION
    | 41 -> OPEN_EFP_COMPUTATION
    | 42 -> HIGH_EFP_COMPUTATION
    | 43 -> LOW_EFP_COMPUTATION
    | 44 -> CLOSE_EFP_COMPUTATION
    | 45 -> LAST_TIMESTAMP
    | 46 -> SHORTABLE
    | 47 -> FUNDAMENTAL_RATIOS
    | 48 -> RT_VOLUME
    | 49 -> HALTED
    | 50 -> BIDYIELD
    | 51 -> ASKYIELD
    | 52 -> LASTYIELD
    | 53 -> CUST_OPTION_COMPUTATION
    | 54 -> TRADE_COUNT
    | 55 -> TRADE_RATE
    | 56 -> VOLUME_RATE

;;

type whatToShow = TRADES
		  | MIDPOINT
		  | BID
		  | ASK
		  | BID_ASK
		  | HISTORICAL_VOLATILITY
		  | OPTION_IMPLIED_VOLATILITY
		  | OPTION_VOLUME
		  | OPTION_OPEN_INTEREST
;;

let whatToShow2strign (w: whatToShow) : string =
  match w with
    | TRADES -> "TRADES"
    | MIDPOINT -> "MIDPOINT"
    | BID -> "BID"
    | ASK -> "ASK"
    | BID_ASK -> "BID_ASK"
    | HISTORICAL_VOLATILITY -> "HISTORICAL_VOLATILITY"
    | OPTION_IMPLIED_VOLATILITY -> "OPTION_IMPLIED_VOLATILITY"
    | OPTION_VOLUME -> "OPTION_VOLUME"
    | OPTION_OPEN_INTEREST -> "OPTION_OPEN_INTEREST"
;;

type mktData = MDTickPrice of tickType * float * int * bool
	       | MDTickSize of tickType * int
	       | MDTickGeneric of tickType * float
	       | MDTickString of tickType * string
;;

open Date;;      

type bar = {
  bstartdt: datetime;
  bopen: float;
  high: float;
  low: float;
  close: float;
  volume: int64;
  average: float;
  hasGaps: string;
  barCount: int;
};;

type histData = {
  startdt: datetime;
  enddt: datetime;
  bars: bar array;
};;

type mktDepthTable = ((float * int * string option) option) array;;

module IBTWS: sig 
    
  type t

  val connect: ?addr:string -> ?port:int -> unit -> t  

  val reqContractDetails: t -> contract -> (contractDetails list -> unit) -> unit

  val reqMktData: t -> contract -> genericTickType list -> bool -> (mktData -> unit) -> int
  val cancelMktData: t -> int -> unit

  (* the handler function arguments correspond to market depth 
     in (bid, ask)
  *)
  val reqMktDepth: t -> contract -> int -> (mktDepthTable * mktDepthTable -> unit) -> int
  val cancelMktDepth: t -> int -> unit

  val reqHistoricalData: t -> contract -> datetime -> duration -> barSize -> whatToShow -> bool -> (histData -> unit) -> unit

  val reqRTBars: t -> contract -> whatToShow -> bool -> (bar -> unit) -> int
  val cancelRTBars: t -> int -> unit

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

    (********************************************************************)

    (* d counter for contractDetails *)
    mutable contractDetailsIds: int;

    (* contract details handler *)
    mutable contractDetailsHandlers: (contractDetails list -> unit) IndexMap.t;

    (* contract details data *)
    mutable contractDetailsData: (contractDetails list) IndexMap.t;

    (********************************************************************)

    (* counter *)
    mutable mktDataIds: int;

    (*  handler *)
    mutable mktDataHandlers: (mktData -> unit) IndexMap.t;

    (********************************************************************)

    (* counter *)
    mutable mktDepthIds: int;
    
    (* handler *)
    mutable mktDepthHandlers: (mktDepthTable * mktDepthTable -> unit) IndexMap.t;
    
    (* data *)
    mutable mktDepthData: (mktDepthTable * mktDepthTable) IndexMap.t;
    
    (********************************************************************)
      
    (* counter *)
    mutable mktHistIds: int;
      
    (* handlers *)
    mutable mktHistHandlers: (histData -> unit) IndexMap.t;

    (********************************************************************)
      
    (* counter *)
    mutable rtBarsIds: int;
      
    (* handlers *)
    mutable rtBarsHandlers: (bar -> unit) IndexMap.t;

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

      mktDataIds = 0;
      mktDataHandlers = IndexMap.empty;

      mktDepthIds = 0;
      mktDepthHandlers = IndexMap.empty;
      mktDepthData = IndexMap.empty;

      mktHistIds = 0;
      mktHistHandlers = IndexMap.empty;

      rtBarsIds = 0;
      rtBarsHandlers = IndexMap.empty;

    };;

  (***********************************************)

  let reqContractDetails data contract handler = 
    let id = data.contractDetailsIds in
    data.contractDetailsIds <- id + 1;
    data.contractDetailsHandlers <- IndexMap.add id handler data.contractDetailsHandlers;
    data.contractDetailsData <- IndexMap.add id [] data.contractDetailsData;
    reqContractDetails id contract data.out_c;;

  (***********************************************)

  let reqMktData data contract genticklist snapshot handler =
    let id = data.mktDataIds in
    data.mktDataIds <- id + 1;
    data.mktDataHandlers <- IndexMap.add id handler data.mktDataHandlers;
    reqMktData id contract (String.concat "," (List.map (fun hd -> string_of_int (genericTickType2Int hd)) genticklist)) snapshot data.out_c;
    id
  ;;

  let cancelMktData data id =
    cancelMktData id data.out_c;
    data.mktDataHandlers <- IndexMap.remove id data.mktDataHandlers    
  ;;

  (***********************************************)

  let reqMktDepth data contract size handler =
    let id = data.mktDepthIds in
    data.mktDepthIds <- id + 1;
    data.mktDepthHandlers <- IndexMap.add id handler data.mktDepthHandlers;
    data.mktDepthData <- IndexMap.add id (Array.make size None, Array.make size None) data.mktDepthData;
    reqMktDepth id contract size data.out_c;
    id
  ;;    

  let cancelMktDepth data id =
    cancelMktDepth id data.out_c;
    data.mktDepthHandlers <- IndexMap.remove id data.mktDepthHandlers;
    data.mktDepthData <- IndexMap.remove id data.mktDepthData;
  ;;

  (***********************************************)

  let reqHistoricalData data contract endDatetime duration barSize whatToShow useRTH handler =
    let id = data.mktHistIds in
    data.mktHistIds <- id + 1;
    data.mktHistHandlers <- IndexMap.add id handler data.mktHistHandlers;
    reqHistoricalData id contract (datetime_to_string endDatetime) (duration2string duration) (barSize2string barSize) (whatToShow2strign whatToShow) (if useRTH then 1 else 0) 0 data.out_c

  (***********************************************)

  let reqRTBars data contract whatToShow useRTH handler =
    let id = data.rtBarsIds in
    data.rtBarsIds <- id + 1;
    data.rtBarsHandlers <- IndexMap.add id handler data.rtBarsHandlers;
    reqRealTimeBars id contract 5 (whatToShow2strign whatToShow) (if useRTH then 1 else 0) data.out_c;
    id

  let cancelRTBars data id =
    cancelRealTimeBars id data.out_c;
    data.rtBarsHandlers <- IndexMap.remove id data.rtBarsHandlers
  ;;

  (***********************************************)

  (* TODO: better error management!!! *)
  let recv_and_process data =
    let msg = processMsg data.in_c in
    match msg with
      (* contractDetails: buffered until end *)
      | ContractData (_, id, cd) -> (
	try (
	  let cds = IndexMap.find id data.contractDetailsData in
	  data.contractDetailsData <- IndexMap.add id (cds @ [cd]) data.contractDetailsData;
	) with 
	  | _ -> ()
      )
      | BondData (_, id, cd) -> (
	try (
	  let cds = IndexMap.find id data.contractDetailsData in
	  data.contractDetailsData <- IndexMap.add id (cds @ [cd]) data.contractDetailsData;
	) with
	  | _ -> ()
      )
      | ContractDataEnd (_, id) -> (
	try (
	  let f = IndexMap.find id data.contractDetailsHandlers in
	  let msgs = IndexMap.find id data.contractDetailsData in
	  data.contractDetailsHandlers <- IndexMap.remove id data.contractDetailsHandlers;
	  data.contractDetailsData <- IndexMap.remove id data.contractDetailsData;
	  f msgs
	) with
	  | _ -> ()
      )
      | TickPrice (_, id, ticktype, price, size, canauto) -> (
	try (
	  let f = IndexMap.find id data.mktDataHandlers in
	  f (MDTickPrice (tickTypeFromInt ticktype, price, size, if canauto = 0 then false else true))
	) with
	  | _ -> ()
      )
      | TickSize (_, id, ticktype, size) -> (
	try (
	  let f = IndexMap.find id data.mktDataHandlers in
	  f (MDTickSize (tickTypeFromInt ticktype, size))
	) with
	  | _ -> ()
      )
      | TickString (_, id, ticktype, value) -> (
	try (
	  let f = IndexMap.find id data.mktDataHandlers in
	  f (MDTickString (tickTypeFromInt ticktype, value))
	) with
	  | _ -> ()
      )
      | TickGeneric (_, id, ticktype, value) -> (
	try (
	  let f = IndexMap.find id data.mktDataHandlers in
	  f (MDTickGeneric (tickTypeFromInt ticktype, value))
	) with
	  | _ -> ()
      )
      | TickSnapshotEnd (_, id) -> (
	try (
	  data.mktDataHandlers <- IndexMap.remove id data.mktDataHandlers
	) with
	  | _ -> ()
      )
      | MktDepth (version, id, position, operation, side, price, size) -> (
	try (
	  let f = IndexMap.find id data.mktDepthHandlers in
	  let d = IndexMap.find id data.mktDepthData in
	  let a = if side = 0 then snd d else fst d in
	  let _ = (
	    match operation with
	      | 0 | 1 -> a.(position) <- Some (price, size, None)
	      | 2 -> a.(position) <- None
	  ) in
	  f d
	) with
	  | _ -> ()
      )
      | MktDepth2 (version, id, position, mktmaker, operation, side, price, size) -> (
	  let f = IndexMap.find id data.mktDepthHandlers in
	  let d = IndexMap.find id data.mktDepthData in
	  let a = if side = 0 then snd d else fst d in
	  let _ = (
	    match operation with
	      | 0 | 1 -> a.(position) <- Some (price, size, Some mktmaker)
	      | 2 -> a.(position) <- None
	  ) in
	  f d
      )
      | HistData (_, id, startdt, enddt, bars) -> (
	try (
	  let f = IndexMap.find id data.mktHistHandlers in
	  data.mktHistHandlers <- IndexMap.remove id data.mktHistHandlers;	  
	  f ({
	    startdt = parse_datetime startdt;
	    enddt = parse_datetime enddt;
	    bars = Array.of_list (List.map (
	      fun (date, bopen, high, low, close, volume, average, hasGaps, barCount) ->
		{ bstartdt = parse_datetime date;
		  bopen = bopen;
		  high = high;
		  low = low;
		  close = close;
		  volume = volume;
		  average = average;
		  hasGaps = hasGaps;
		  barCount = barCount;
		}
	    ) bars)

	  })
	) with 
	  | _ -> ()
      )
      | RTBar (_, id, startdt, bopen, high, low, close, volume, average, count) -> (
	try (
	  let f = IndexMap.find id data.rtBarsHandlers in
	  f ({ bstartdt =( let dtm = Unix.gmtime (Int64.to_float startdt) in
			  { year = dtm.tm_year;
			    mounth = dtm.tm_mon+1;
			    day = dtm.tm_mday;
			    hour = dtm.tm_hour;
			    minute = dtm.tm_min;
			    second = dtm.tm_sec;
			    tz = "UTC";
			  });
	       bopen = bopen;
	       high = high;
	       low = low;
	       close = close;
	       volume = volume;
	       average = average;
	       hasGaps = "";
	       barCount = count;
	     })
	) with 
	  | _ -> ()
      )
      | _ -> raise (Failure "recv_and_process: msg not yet supported")
;;


end;;
