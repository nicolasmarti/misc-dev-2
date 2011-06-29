open Unix;;
open Encdec;;
open Pervasives;;
open Contract;;
open Printf;;
open Scannersubscription;;
open Order;;
open Connect;;
open Execution;;

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
let historical_data = 17;;
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

type version = int;;
type id = int;;

type msg = ErrMsg of version * id * int * string

	   | NextValidId of version * id 

	   | TickPrice of version * id * int * float * int * int
	   | TickSize of version * id * int * int
	   | TickString of version * id * int * string
	   | TickGeneric of version * id * int * float
	   | TickSnapshotEnd of version * id

	   | MktDepth of version * id * int * int * int * float * int
	   | MktDepth2 of version * id * int * string * int * int * float * int

	   | HistData of version * id * string * string * (string * float * float * float * float * int64 * float * string * int) list

	   | RTBar of version * id * int64 * float * float * float * float * int64 * float * int

	   | ScannerParams of version * string
	   | ScannerData of version * id * scanData array

	   | FundamentalData of version * id * string

	   | ContractData of version * id * contractDetails
	   | BondData of version * id * contractDetails
	   | ContractDataEnd of version * id

	   | CurrentTime of version * int

	   | OrderStatus of version * id * string * int * int * float * int * int * float * int * string
	   | OpenOrder of version * order * contract * orderState

	   | AccountValue of version * string * string * string * string
	   | PortFolioValue of version * contract * int * float * float * float * float * float * string
	   | AccountUpdateTime of version * string
	   | AccountDownloadEnd of version * string

	   | ExecutionData of version * id * int64 * contract * execution 
	   | OpenOrderEnd of version
	   | ExecutionDataEnd of version * id

;;

(* EClientSocketBase::processMsg *)

let processMsg (ic: in_channel) : msg =
  let msgId = decode_int ic in
  (*printf "msgid = %d\n" msgId;*)
    match msgId with
      | 4 (*err_msg*) -> (
	  let version = decode_int ic in
	  let id = decode_int ic in
	  let errCode = decode_int ic in
	  let errMsg = decode_string ic in
	  printf "%s\n" errMsg;
	  ErrMsg (version, id, errCode, errMsg) 
	)
      | 1 (*tick_price*) -> (
	  let version = decode_int ic in
	  let tickerId = decode_int ic in
	  let tickTypeInt = decode_int ic in
	  let price = decode_float ic in
	  let size = decode_int ic in
	  let canAutoExecute = decode_int ic in
	  TickPrice (version, tickerId, tickTypeInt, price, size, canAutoExecute)
	)
      | 2 (*tick_size*) -> (
	  let version = decode_int ic in
	  let tickerId = decode_int ic in
	  let tickTypeInt = decode_int ic in
	  let size = decode_int ic in
	    TickSize (version, tickerId, tickTypeInt, size)
	)
      | 9 (*next_valid_id*) -> (
	  let version = decode_int ic in
	  let orderId = decode_int ic in
	  currId := orderId;
	  NextValidId (version, orderId)
	)
      | 46 (*tick_string *) -> (
	  let version = decode_int ic in
	  let tickerId = decode_int ic in
	  let tickTypeInt = decode_int ic in
	  let value = decode_string ic in
	  TickString (version, tickerId, tickTypeInt, value)
	)
      | 45 (* tick_generic *) -> (
	  let version = decode_int ic in
	  let tickerId = decode_int ic in
	  let tickTypeInt = decode_int ic in
	  let value = decode_float ic in
	  TickGeneric (version, tickerId, tickTypeInt, value)
	)
      | 57 (* tick_snapshot_end *) -> (
	  let version = decode_int ic in
	  let reqId = decode_int ic in
	  TickSnapshotEnd (version, reqId)	    
	)

      | 12 (* market_depth *) -> (
	  let version = decode_int ic in
	  let id = decode_int ic in
	  let position = decode_int ic in
	  let operation = decode_int ic in
	  let side = decode_int ic in
	  let price = decode_float ic in
	  let size = decode_int ic in
	    MktDepth (version, id, position, operation, side, price, size)
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
	    MktDepth2 (version, id, position, marketMaker, operation, side, price, size)
	)
      | 17 (* historical_data *) -> (
	  let version = decode_int ic in
	  let reqId = decode_int ic in
	  let startDateStr = decode_string ic in
	  let endDateStr = decode_string ic in
	    (*printf "Historical data (%d, %d, %s, %s)\n" version reqId startDateStr endDateStr;*)
	    let itemCount = ref (decode_int ic) in
	    let bars = ref [] in
	      while !itemCount > 0 do
		let date = decode_string ic in
		let bopen = decode_float ic in
		let high = decode_float ic in
		let low = decode_float ic in
		let close = decode_float ic in
		let volume = decode_int64 ic in
		let average = decode_float ic in
		let hasGaps = decode_string ic in
		let barCount = decode_int ic in
		(*printf "HistoricalData(%s, %f, %f, %f, %f, %d, %f, %s, %d)\n" date bopen high low close volume average hasGaps barCount;*)
		bars := (date, bopen, high, low, close, volume, average, hasGaps, barCount)::!bars;
		itemCount := !itemCount - 1;
	      done;	    
	    HistData (version, reqId, startDateStr, endDateStr, !bars)

	)
      | 50 (* real_time_bars *) -> (
	  let version = decode_int ic in
	  let reqId = decode_int ic in
	  let time = decode_int64 ic in

	  let bopen = decode_float ic in
	  let high = decode_float ic in
	  let low = decode_float ic in
	  let close = decode_float ic in
	  let volume = decode_int64 ic in
	  let average = decode_float ic in
	  let count = decode_int ic in
	
	  RTBar (version, reqId, time, bopen, high, low, close, volume, average, count)
      )
      | 19 (* scanner_parameters *) -> (
	let version = decode_int ic in
	let xml = decode_string ic in
	ScannerParams (version, xml)
      )	  
      | 20 (* scanner_data *) -> (
	  let version = decode_int ic in
	  let reqId = decode_int ic in
	  let numberOfElements = decode_int ic in
	  let res = Array.init numberOfElements (fun _ -> build_scanData ()) in
	  let index = ref 0 in
	  while !index < numberOfElements do 
	    res.(!index).rank <- decode_int ic;
	    res.(!index).con.summary.conId <- decode_int64 ic;
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
	  done;
	  ScannerData (version, reqId, res)
      )
      | 51 (* FUNDAMENTAL_DATA *) -> (
	let version = decode_int ic in
	let reqId = decode_int ic in
	let data = decode_string ic in
	FundamentalData (version, reqId, data)
      )
      | 10 (* CONTRACT_DATA *) -> (
	let version = decode_int ic in
	let reqId = if version >= 3 then decode_int ic else -1 in
	let con = build_contractDetails () in
	con.summary.symbol <- decode_string ic;
	con.summary.secType <- decode_string ic;
	con.summary.expiry <- decode_string ic;
	con.summary.strike <- decode_float ic;
	con.summary.right <- decode_string ic;
	con.summary.exchange <- decode_string ic;
	con.summary.currency <- decode_string ic;
	con.summary.localSymbol <- decode_string ic;
	con.marketName <- decode_string ic;
	con.tradingClass <- decode_string ic;
	con.summary.conId <- decode_int64 ic;
	con.minTick <- decode_float ic;
	con.summary.multiplier <- decode_string ic;
	con.orderTypes <- decode_string ic;
	con.validExchanges <- decode_string ic;
	con.priceMagnifier <- decode_int ic;
	
	if version >= 4 then
	  con.underConId <- decode_int ic;

	if version >= 5 then (
	  con.longName <- decode_string ic;
	  con.summary.primaryExchange <- decode_string ic;
	);

	if version >= 6 then (
	  con.contractMonth <- decode_string ic;
	  con.industry <- decode_string ic;
	  con.category <- decode_string ic;
	  con.subcategory <- decode_string ic;
	  con.timeZoneId <- decode_string ic;
	  con.tradingHours <- decode_string ic;
	  con.liquidHours <- decode_string ic;
	);
	ContractData (version, reqId, con)
      )
      | 18 (* BOND_CONTRACT_DATA *) -> (

	let version = decode_int ic in
	let reqId = if version >= 3 then decode_int ic else -1 in
	let con = build_contractDetails () in

	con.summary.symbol <- decode_string ic;
	con.summary.secType <- decode_string ic;
	con.cusip <- decode_string ic;
	con.coupon <- decode_float ic;
	con.maturity <- decode_string ic;
	con.issueDate <- decode_string ic;
	con.ratings <- decode_string ic;
	con.bondType <- decode_string ic;
	con.couponType <- decode_string ic;
	con.convertible <- decode_bool ic;
	con.callable <- decode_bool ic;
	con.putable <- decode_bool ic;
	con.descAppend <- decode_string ic;
	con.summary.exchange <- decode_string ic;
	con.summary.currency <- decode_string ic;
	con.marketName <- decode_string ic;
	con.tradingClass <- decode_string ic;
	con.summary.conId <- decode_int64 ic;
	con.minTick <- decode_float ic;
	con.orderTypes <- decode_string ic;
	con.validExchanges <- decode_string ic;
	con.nextOptionDate <- decode_string ic;
	con.nextOptionType <- decode_string ic;
	con.nextOptionPartial <- decode_bool ic;
	con.notes <- decode_string ic;
	if version >= 4 then
	  con.longName <- decode_string ic;
	BondData (version, reqId, con)
      )
      | 52 (* CONTRACT_DATA_END *) -> (
	let version = decode_int ic in
	let reqId = decode_int ic in
	ContractDataEnd (version, reqId)
      )
      | 49 (* CURRENT_TIME *) -> (
	let version = decode_int ic in
	let time = decode_int ic in
	CurrentTime (version, time)
      )
      | 3 (* ORDER_STATUS *) -> (
	let version = decode_int ic in
	let orderId = decode_int ic in
	let status = decode_string ic in
	let filled = decode_int ic in
	let remaining = decode_int ic in
	let avgFillPrice = decode_float ic in
	
	let permId = decode_int ic in
	let parentId = decode_int ic in
	let lastFillPrice = decode_float ic in
	let clientId = decode_int ic in
	let whyHeld = decode_string ic in
	
	OrderStatus (version, orderId, status, filled, remaining, avgFillPrice, permId, parentId, lastFillPrice, clientId, whyHeld)
	
      )
      | 5 (* OPEN_ORDER *) -> (
	let version = decode_int ic in
	let o = build_order () in
	o.orderId <- decode_int64 ic;
	let c = build_contract () in
	c.conId <- decode_int64 ic;
	c.symbol <- decode_string ic;
	c.secType <- decode_string ic;
	c.expiry <- decode_string ic;
	c.strike <- decode_float ic;
	c.right <- decode_string ic;
	c.exchange <- decode_string ic;
	c.currency <- decode_string ic;
	c.localSymbol <- decode_string ic;

	o.oaction <- decode_string ic;
	o.totalQuantity <- decode_int64 ic;
	o.orderType <- decode_string ic;
	o.lmtPrice <- decode_float ic;
	o.auxPrice <- decode_float ic;
	o.tif <- decode_string ic;
	o.ocaGroup <- decode_string ic;
	o.account <- decode_string ic;
	o.oopenClose <- decode_string ic;

	o.origin <- decode_int ic;
	o.orderRef <- decode_string ic;
	o.clientId <- decode_int64 ic;
	o.permId <- decode_int64 ic;

	o.outsideRth <- decode_bool ic;
	o.hidden <- decode_bool ic;
	o.discretionaryAmt <- decode_float ic;
	o.goodAfterTime <- decode_string ic;
	
	ignore (decode_string ic);

	o.faGroup <- decode_string ic;
	o.faMethod <- decode_string ic;
	o.faPercentage <- decode_string ic;
	o.faProfile <- decode_string ic;

	o.goodTillDate <- decode_string ic;

	o.rule80A <- decode_string ic;
	o.percentOffset <- decode_float ic;
	o.settlingFirm <- decode_string ic;
	o.oshortSaleSlot <- decode_int ic;
	o.odesignatedLocation <- decode_string ic;
	
	if !server_version = 51 (* MIN_SERVER_VER_SSHORTX_OLD *) then
	  ignore (decode_int ic)
	else
	  o.oexemptCode <- decode_int ic;
	
	o.auctionStrategy <- decode_int ic;
	o.startingPrice <- decode_float ic;
	o.stockRefPrice <- decode_float ic;
	o.odelta <- decode_float ic;
	o.stockRangeLower <- decode_float ic;
	o.stockRangeUpper <- decode_float ic;
	o.displaySize <- decode_int ic;

	o.blockOrder <- decode_bool ic;
	o.sweepToFill <- decode_bool ic;
	o.allOrNone <- decode_bool ic;
	o.minQty <- decode_int ic;
	o.ocaType <- decode_int ic;
	o.eTradeOnly <- decode_bool ic;
	o.firmQuoteOnly <- decode_bool ic;
	o.nbboPriceCap <- decode_float ic;

	o.parentId <- decode_int64 ic;
	o.triggerMethod <- decode_int ic;

	o.volatility <- decode_float ic;
	o.volatilityType <- decode_int ic;
	o.deltaNeutralOrderType <- decode_string ic;
	o.deltaNeutralAuxPrice <- decode_float ic;
	o.continuousUpdate <- decode_bool ic;
	
	o.referencePriceType <- decode_int ic;

	o.trailStopPrice <- decode_float ic;

	o.basisPoints <- decode_float ic;
	o.basisPointsType <- decode_int ic;
	c.comboLegsDescrip <- decode_string ic;

	if !server_version >= 20 then (
	  o.scaleInitLevelSize <- decode_int_max ic;
	  o.scaleSubsLevelSize <- decode_int_max ic;
	) else (
	  ignore (decode_int_max ic);
	  o.scaleInitLevelSize <- decode_int_max ic;
	);

	o.scalePriceIncrement <- decode_float_max ic;

	o.clearingAccount <- decode_string ic;
	o.clearingIntent <- decode_string ic;

	if !server_version >= 22 then
	  o.notHeld <- decode_bool ic;

	if !server_version >= 20 then (
	  if decode_bool ic then
	    (
	      let uc = build_underComp () in
	      uc.uc_conId <- decode_int64 ic;
	      uc.delta <- decode_float ic;
	      uc.price <- decode_float ic;
	      c.undercomp <- Some uc
	    )
	);

	if !server_version >= 21 then (
	  o.algoStrategy <- decode_string ic;
	  if String.length o.algoStrategy > 0 then (
	    let algoParamsCount = decode_int ic in
	    let index = ref 0 in
	    while !index < algoParamsCount do
	      let tag = decode_string ic in
	      let value = decode_string ic in
	      o.algoParams <- o.algoParams @ [tag, value];
	    done
	  )
	);

	o.whatIf <- decode_bool ic;
	
	let os = build_orderState () in

	os.status <- decode_string ic;
	os.initMargin <- decode_string ic;
	os.maintMargin <- decode_string ic;
	os.equityWithLoan <- decode_string ic;
	os.commission <- decode_float_max ic;
	os.minCommission <- decode_float_max ic;
	os.maxCommission <- decode_float_max ic;
	os.commissionCurrency <- decode_string ic;
	os.warningText <- decode_string ic;

	OpenOrder (version, o, c, os)
      )
      | 6 (* ACCT_VALUE *) -> (
	let version = decode_int ic in
	let key = decode_string ic in
	let value = decode_string ic in 
	let cur = decode_string ic in
	let accountName = decode_string ic in
	AccountValue (version, key, value, cur, accountName)
      )
      | 7 (* PORTFOLIO_VALUE *) -> (
	let version = decode_int ic in
	let c = build_contract () in
	c.conId <- decode_int64 ic;
	c.symbol <- decode_string ic;
	c.secType <- decode_string ic;
	c.expiry <- decode_string ic;
	c.strike <- decode_float ic;
	c.right <- decode_string ic;

	if !server_version >= 7 then (
	  c.multiplier <- decode_string ic;
	  c.primaryExchange <- decode_string ic;
	);

	c.currency <- decode_string ic;
	c.localSymbol <- decode_string ic;

	let position = decode_int ic in
	let marketPrice = decode_float ic in
	let marketValue = decode_float ic in
	let averageCost = decode_float ic in
	let unrealizedPNL = decode_float ic in
	let realizedPNL = decode_float ic in
	let accountName = decode_string ic in

	if !server_version = 6 && !server_version = 39 then (
	  c.primaryExchange <- decode_string ic
	);

	PortFolioValue (version, c, position, marketPrice, marketValue, averageCost, unrealizedPNL, realizedPNL, accountName)
      )
      | 8 (* ACCT_UPDATE_TIME *) -> (
	let version = decode_int ic in
	let accountName = decode_string ic in
	AccountUpdateTime (version, accountName)
      )
      | 11 (* EXECUTION_DATA *) -> (
	let version = decode_int ic in
	let reqId = if !server_version >= 7 then decode_int ic else -1 in
	let orderId = decode_int64 ic in
	let c = build_contract () in
	
	c.conId <- decode_int64 ic;
	c.symbol <- decode_string ic;
	c.secType <- decode_string ic;
	c.expiry <- decode_string ic;
	c.strike <- decode_float ic;
	c.right <- decode_string ic;
	c.exchange <- decode_string ic;
	c.currency <- decode_string ic;
	c.localSymbol <- decode_string ic;

	let e = build_execution () in
	e.ex_orderId <- orderId;
	e.execId <- decode_string ic;
	e.ex_time <- decode_string ic;
	e.acctNumber <- decode_string ic;
	e.ex_exchange <- decode_string ic;
	e.ex_side <- decode_string ic;
	e.shares <- decode_int ic;
	e.ex_price <- decode_float ic;
	e.ex_permId <- decode_int64 ic;
	e.ex_clientId <- decode_int64 ic;
	e.liquidation <- decode_int ic;
	
	if !server_version >= 6 then (
	  e.cumQty <- decode_int ic;
	  e.avgPrice <- decode_float ic;
	);

	ExecutionData (version, reqId, orderId, c, e)
      )
      | 53 (* OPEN_ORDER_END *) -> (
	let version = decode_int ic in
	OpenOrderEnd version
      )
      | 54 (* ACCT_DOWNLOAD_END *) -> (
	let version = decode_int ic in
	let account = decode_string ic in
	AccountDownloadEnd (version, account)
      )
      | 55 (* EXECUTION_DATA_END *) -> (
	let version = decode_int ic in
	let reqId = decode_int ic in
	ExecutionDataEnd (version, reqId)
      )
      | id -> (
	printf "%s\n" (String.concat " " ["not yet supported:";(string_of_int id)]);
	raise (Failure (String.concat " " ["not yet supported:";(string_of_int id)]))
      )
;;


