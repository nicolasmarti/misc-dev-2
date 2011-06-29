open Encdec;;
open Unix;;
open Contract;;
open Connect;;
open Order;;

let req_mkt_data = 1;;
let cancel_mkt_data = 2;;
let place_order = 3;;
let cancel_order = 4;;
let req_open_orders = 5;;
let req_acct_data = 6;;
let req_executions = 7;;
let req_ids = 8;;
let req_contract_data = 9;;
let req_mkt_depth = 10;;
let cancel_mkt_depth = 11;;
let req_news_bulletins = 12;;
let cancel_news_bulletins = 13;;
let set_server_loglevel = 14;;
let req_auto_open_orders = 15;;
let req_all_open_orders = 16;;
let req_managed_accts = 17;;
let req_fa = 18;;
let replace_fa = 19;;
let req_historical_data = 20;;
let exercise_options = 21;;
let req_scanner_subscription = 22;;
let cancel_scanner_subscription = 23;;
let req_scanner_parameters = 24;;
let cancel_historical_data = 25;;
let req_current_time = 49;;
let req_real_time_bars = 50;;
let cancel_real_time_bars = 51;;
let req_fundamental_data = 52;;
let cancel_fundamental_data = 53;;
let req_global_cancel = 58;;

let reqIds (numIds: int) (oc: out_channel) : unit =
  encode_int req_ids oc;
  encode_int 1 oc;
  encode_int numIds oc;
  flush oc
;;

let reqMktData (tickerId: int) (c: contract) (genericTicks: string) (snapshot: bool) (oc: out_channel) : unit =

  let version = 9 in
    encode_int req_mkt_data oc;
    encode_int version oc;
    encode_int tickerId oc;

    if !server_version > 47 then
	encode_int64 c.conId oc;

    encode_string c.symbol oc;
    encode_string c.secType oc;
    encode_string c.expiry oc;
    encode_float c.strike oc;
    encode_string c.right oc;
    encode_string c.multiplier oc;

    encode_string c.exchange oc;
    encode_string c.primaryExchange oc;
    encode_string c.currency oc;

    encode_string c.localSymbol oc;
    
    if c.secType = "BAG" then (

      if List.length c.comboLegs = 0 then
	encode_int 0 oc
      else (
	encode_int (List.length c.comboLegs) oc;
	
	ignore (List.map (
	  fun hd ->
	    encode_int64 hd.cl_conId oc;
	    encode_int hd.ratio oc;
	    encode_string hd.action oc;
	    encode_string hd.cl_exchange oc;
	) c.comboLegs)

      );
	
    );

    if !server_version >= 40 then (
      match c.undercomp with
	| None -> encode_bool false oc
	| Some uc -> (
	  encode_bool true oc;
	  encode_int64 uc.uc_conId oc;
	  encode_float uc.delta oc;
	  encode_float uc.price oc;
	);      

    );

    encode_string genericTicks oc;

    encode_bool snapshot oc;

    flush oc
;;

let cancelMktData (tickerId: int) (oc: out_channel) : unit =
  let version = 2 in
    encode_int cancel_mkt_data oc;
    encode_int version oc;
    encode_int tickerId oc;
    flush oc
;;

let reqMktDepth (tickerId: int) (c: contract) (numRows: int)  (oc: out_channel): unit =
  let version = 3 in
    encode_int req_mkt_depth oc;
    encode_int version oc;
    encode_int tickerId oc;
    
    encode_string c.symbol oc;
    encode_string c.secType oc;
    encode_string c.expiry oc;
    encode_float c.strike oc;
    encode_string c.right oc;
    encode_string c.multiplier oc;
    encode_string c.exchange oc;
    encode_string c.currency oc;
    encode_string c.localSymbol oc;
    
    encode_int numRows oc;
    
    flush oc
;;

let cancelMktDepth (tickerId: int)  (oc: out_channel): unit =
  let version = 1 in
    encode_int cancel_mkt_depth oc;
    encode_int version oc;
    encode_int tickerId oc;

    flush oc
;;

    
let reqHistoricalData (tickerId: int) (c: contract) (endDateTime: string) (durationStr: string) (barSizeSetting: string) (whatToShow: string) (useRTH: int) (formatDate: int) (oc: out_channel) : unit =
  let version = 4 in
    encode_int req_historical_data oc;
    encode_int version oc;
    encode_int tickerId oc;

    encode_string c.symbol oc;
    encode_string c.secType oc;
    encode_string c.expiry oc;
    encode_float c.strike oc;
    encode_string c.right oc;
    encode_string c.multiplier oc;
    encode_string c.exchange oc;
    encode_string c.primaryExchange oc;
    encode_string c.currency oc;
    encode_string c.localSymbol oc;
    encode_bool c.includeExpired oc;
    
    encode_string endDateTime oc;
    encode_string barSizeSetting oc;
    
    encode_string durationStr oc;
    encode_int useRTH oc;
    encode_string whatToShow oc;
    encode_int formatDate oc;

    if c.secType = "BAG" then (

      if List.length c.comboLegs = 0 then
	encode_int 0 oc
      else (
	encode_int (List.length c.comboLegs) oc;
	
	ignore (List.map (
	  fun hd ->
	    encode_int64 hd.cl_conId oc;
	    encode_int hd.ratio oc;
	    encode_string hd.action oc;
	    encode_string hd.cl_exchange oc;
	) c.comboLegs)

      );
	
    );

    flush oc
;;

let cancelHistoricalData (tickerId: int) (oc: out_channel) : unit =
  let version = 1 in
    encode_int cancel_historical_data oc;
    encode_int version oc;
    encode_int tickerId oc;
    
    flush oc
;;

let reqRealTimeBars (tickerId: int) (c: contract) (barsize: int) (whatToShow: string) (useRTH: int) (oc: out_channel) : unit =
  let version = 1 in
    encode_int req_real_time_bars oc;
    encode_int version oc;
    encode_int tickerId oc;
    
    encode_string c.symbol oc;
    encode_string c.secType oc;
    encode_string c.expiry oc;
    encode_float c.strike oc;
    encode_string c.right oc;
    encode_string c.multiplier oc;
    encode_string c.exchange oc;
    encode_string c.primaryExchange oc;
    encode_string c.currency oc;
    encode_string c.localSymbol oc;

    encode_int barsize oc;
    encode_string whatToShow oc;
    encode_int useRTH oc;

    flush oc
;;

let cancelRealTimeBars (tickerId: int) (oc: out_channel) : unit =
  let version = 1 in
    encode_int cancel_real_time_bars oc;
    encode_int version oc;
    encode_int tickerId oc;
    
    flush oc
;;


let reqScannerParameters (oc: out_channel) : unit =
  let version = 1 in
    encode_int req_scanner_parameters oc;
    encode_int version oc;
    
    flush oc
;;

open Scannersubscription;;

let reqScannerSubscription (tickerId: int) (subscription: scannerSubscription) (oc: out_channel) : unit =
  let version = 3 in
  encode_int req_scanner_subscription oc;
  encode_int version oc;
  encode_int tickerId oc;
  encode_int_max subscription.numberOfRows oc;
  encode_string subscription.instrument oc;
  encode_string subscription.locationCode oc;
  encode_string subscription.scanCode oc;
  encode_float_max subscription.abovePrice oc;
  encode_float_max subscription.belowPrice oc;
  encode_int_max subscription.aboveVolume oc;
  encode_float_max subscription.marketCapAbove oc;
  encode_float_max subscription.marketCapBelow oc;
  encode_string subscription.moodyRatingAbove oc;
  encode_string subscription.moodyRatingBelow oc;
  encode_string subscription.spRatingAbove oc;
  encode_string subscription.spRatingBelow oc;
  encode_string subscription.maturityDateAbove oc;
  encode_string subscription.maturityDateBelow oc;
  encode_float_max subscription.couponRateAbove oc;
  encode_float_max subscription.couponRateBelow oc;
  encode_bool subscription.excludeConvertible oc;
  encode_int_max subscription.averageOptionVolumeAbove oc;
  encode_string subscription.scannerSettingPairs oc;
  encode_string subscription.stockTypeFilter oc;

  flush oc
;;

let cancelScannerSubscription (tickerId: int) (oc: out_channel) : unit =
  let version = 1 in
  encode_int cancel_scanner_subscription oc;
  encode_int version oc;
  encode_int tickerId oc;

  flush oc
;;

let reqFundamentalData (tickerId: int) (con: contract) (reportType: string) (oc: out_channel) : unit =
  let version = 1 in
  encode_int req_fundamental_data oc;
  encode_int version oc;
  encode_int tickerId oc;
  
  encode_string con.symbol oc;
  encode_string con.secType oc;
  encode_string con.exchange oc;
  encode_string con.primaryExchange oc;
  encode_string con.currency oc;
  encode_string con.localSymbol oc;
  encode_string reportType oc;

  flush oc
;;

let cancelFundamentalData (tickerId: int) (oc: out_channel) : unit =
  let version = 1 in
  encode_int cancel_fundamental_data oc;
  encode_int version oc;
  encode_int tickerId oc;

  flush oc
;;

let reqContractDetails (reqId: int) (con: contract) (oc: out_channel) : unit =
  let version = 6 in
  encode_int req_contract_data oc;
  encode_int version oc;
  if !server_version >= 40 (*MIN_SERVER_VER_CONTRACT_DATA_CHAIN*) then
    encode_int reqId oc;

  encode_int64 con.conId oc;
  encode_string con.symbol oc;
  encode_string con.secType oc;
  encode_string con.expiry oc;
  encode_float con.strike oc;
  encode_string con.right oc;
  encode_string con.multiplier oc;
  encode_string con.exchange oc;
  encode_string con.currency oc;
  encode_string con.localSymbol oc;
  encode_bool con.includeExpired oc;

  if !server_version >= 45 (* MIN_SERVER_VER_SEC_ID_TYPE *) then (
    encode_string con.secIdType oc;
    encode_string con.secId oc;
  );  

  flush oc
;;

let reqCurrentTime (oc: out_channel) : unit =
  let version = 1 in
  encode_int req_current_time oc;
  encode_int version oc;

  flush oc
;;


let placeOrder (orderId: int) (con: contract) (o: order) (oc: out_channel) : unit =
  let version = (if !server_version < 44 (* MIN_SERVER_VER_NOT_HELD *) then 27 else 31) in

  encode_int place_order oc;
  encode_int version oc;
  encode_int orderId oc;

  if !server_version >= 46 (* MIN_SERVER_VER_PLACE_ORDER_CONID *) then 
    encode_int64 con.conId oc;

  encode_string con.symbol oc;
  encode_string con.secType oc;
  encode_string con.expiry oc;
  encode_float con.strike oc;
  encode_string con.right oc;
  encode_string con.multiplier oc;
  encode_string con.exchange oc;
  encode_string con.primaryExchange oc;
  encode_string con.currency oc;
  encode_string con.localSymbol oc;

  if !server_version >= 45 (* MIN_SERVER_VER_SEC_ID_TYPE *) then (
    encode_string con.secIdType oc;
    encode_string con.secId oc;
  );

  encode_string o.oaction oc;
  encode_int64 o.totalQuantity oc;
  encode_string o.orderType oc;
  encode_float o.lmtPrice oc;
  encode_float o.auxPrice oc;

  encode_string o.tif oc;
  encode_string o.ocaGroup oc;
  encode_string o.account oc;
  encode_string o.oopenClose oc;
  encode_int o.origin oc;
  encode_string o.orderRef oc;
  encode_bool o.transmit oc;
  encode_int64 o.parentId oc;

  encode_bool o.blockOrder oc;
  encode_bool o.sweepToFill oc;
  encode_int o.displaySize oc;
  encode_int o.triggerMethod oc;

  encode_bool o.outsideRth oc;
  encode_bool o.hidden oc;

  if con.secType = "BAG" then (
    
    if List.length con.comboLegs = 0 then
      encode_int 0 oc
    else (
      encode_int (List.length con.comboLegs) oc;
      
      ignore (List.map (
	fun hd ->
	  encode_int64 hd.cl_conId oc;
	  encode_int hd.ratio oc;
	  encode_string hd.action oc;
	  encode_string hd.cl_exchange oc;
	  encode_int hd.openClose oc;

	  encode_int hd.shortSaleSlot oc;
	  encode_string hd.designatedLocation oc;

	  if !server_version >= 51 (* MIN_SERVER_VER_SSHORTX_OLD *) then
	    encode_int hd.exemptCode oc;

      ) con.comboLegs)
	
    );
    
  );

  encode_string "" oc;

  encode_float o.discretionaryAmt oc;
  encode_string o.goodAfterTime oc;
  encode_string o.goodTillDate oc;
  
  encode_string o.faGroup oc;
  encode_string o.faMethod oc;
  encode_string o.faPercentage oc;
  encode_string o.faProfile oc;
 
  encode_int o.oshortSaleSlot oc;
  encode_string o.odesignatedLocation oc;
  if !server_version >=  51 (* MIN_SERVER_VER_SSHORTX_OLD *) then
    encode_int o.oexemptCode oc;

  encode_int o.ocaType oc;
  
  encode_string o.rule80A oc;
  encode_string o.settlingFirm oc;
  encode_bool o.allOrNone oc;
  encode_int_max o.minQty oc;
  encode_float_max o.percentOffset oc;
  encode_bool o.firmQuoteOnly oc;
  encode_float_max o.nbboPriceCap oc;
  encode_int o.auctionStrategy oc;
  encode_float_max o.startingPrice oc;
  encode_float_max o.stockRefPrice oc;
  encode_float_max o.odelta oc;
  encode_float_max o.stockRangeLower oc;
  encode_float_max o.stockRangeUpper oc;

  encode_bool o.overridePercentageConstraints oc;

  encode_float_max o.volatility oc;
  encode_int_max o.volatilityType oc;

  encode_string o.deltaNeutralOrderType oc;
  encode_float o.deltaNeutralAuxPrice oc;

  encode_bool o.continuousUpdate oc;

  encode_int_max o.referencePriceType oc;
  
  encode_float o.trailStopPrice oc;

  if !server_version >= 40 (* MIN_SERVER_VER_SCALE_ORDERS2 *) then (
    encode_int_max o.scaleInitLevelSize oc;
    encode_int_max o.scaleSubsLevelSize oc;
  ) else (
    encode_string "" oc;
    encode_int_max o.scaleInitLevelSize oc;
  );
    
  encode_float_max o.scalePriceIncrement oc;

  if !server_version >= 39 (* MIN_SERVER_VER_PTA_ORDERS *) then (
    encode_string o.clearingAccount oc;
    encode_string o.clearingIntent oc;
  );

  if !server_version >= 44 (* MIN_SERVER_VER_NOT_HELD *) then
    encode_bool o.notHeld oc;

  if !server_version >= 40 (* MIN_SERVER_VER_UNDER_COMP *) then (
    match con.undercomp with
      | None -> encode_bool false oc;
      | Some uc -> 
	encode_bool true oc;
	encode_int64 uc.uc_conId oc;
	encode_float uc.delta oc;
	encode_float uc.price oc;
  );

  if !server_version >= 41 (* MIN_SERVER_VER_ALGO_ORDERS *) then (
    encode_string o.algoStrategy oc;
    
    if String.length o.algoStrategy > 0 then (

      let algoParamsCount = List.length o.algoParams in
      encode_int algoParamsCount oc;
      ignore (List.map (fun hd ->
	encode_string (fst hd) oc;
	encode_string (snd hd) oc;
      ) o.algoParams);
      
    );

  );

  encode_bool o.whatIf oc;

  flush oc
;;

let cancelOrder (id: int) (oc: out_channel) : unit =
  
  let version = 1 in

  encode_int cancel_order oc;
  encode_int version oc;
  encode_int id oc;

  flush oc
;;

let reqAccountUpdates (subscribe: bool) (acctCode: string) (oc: out_channel) : unit =
  
  let version = 2 in

  encode_int req_acct_data oc;
  encode_int version oc;
  encode_bool subscribe oc;

  encode_string acctCode oc;

  flush oc
;;

let reqOpenOrders (oc: out_channel) : unit =

  let version = 1 in

  encode_int req_open_orders oc;
  encode_int version oc;

  flush oc
;;
  
let reqAutoOpenOrders (bAutoBind: bool) (oc: out_channel) : unit =

  let version = 1 in

  encode_int req_auto_open_orders oc;
  encode_int version oc;
  encode_bool bAutoBind oc;

  flush oc
;;

let reqAllOpenOrders (oc: out_channel) : unit =
  let version = 1 in

  encode_int req_all_open_orders oc;
  encode_int version oc;

  flush oc
;;
  
open Execution;;

let reqExecutions (reqId: int) (filter: executionFilter) (oc: out_channel) : unit =
  let version = 3 in
  encode_int req_executions oc;
  encode_int version oc;
  
  if !server_version >= 42 (*MIN_SERVER_VER_EXECUTION_DATA_CHAIN*) then
    encode_int reqId oc;

  encode_int64 filter.ef_clientId oc;
  encode_string filter.acctCode oc;
  encode_string filter.ef_time oc;
  encode_string filter.ef_symbol oc;
  encode_string filter.ef_secType oc;
  encode_string filter.ef_exchange oc;
  encode_string filter.ef_side oc;

  flush oc
;;

let exerciseOPtions (tickerId: int) (c: contract) (exerciseAction: int) (exerciseQuantity: int) (account: string) (override: int) (oc: out_channel) : unit =
  let version = 1 in
  encode_int exercise_options oc;
  encode_int version oc;
  encode_int tickerId oc;

  encode_string c.symbol oc;
  encode_string c.secType oc;
  encode_string c.expiry oc;
  encode_float c.strike oc;
  encode_string c.right oc;
  encode_string c.multiplier oc;
  encode_string c.exchange oc;
  encode_string c.currency oc;
  encode_string c.localSymbol oc;
  encode_int exerciseAction oc;
  encode_int exerciseQuantity oc;
  encode_string account oc;
  encode_int override oc;

  flush oc
;;

let reqGlobalCancel  (oc: out_channel) : unit =
  let version = 1 in
  encode_int req_global_cancel oc;
  encode_int version oc;

  flush oc
;;
















