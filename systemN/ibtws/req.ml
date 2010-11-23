open Encdec;;
open Unix;;
open Contract;;

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

let reqIds (numIds: int) (oc: out_channel) : unit =
  encode_int req_ids oc;
  encode_int 1 oc;
  encode_int numIds oc;
  flush oc
;;

let reqMktData (tickerId: int) (c: contract) (genericTicks: string) (snapshot: bool) (oc: out_channel) : unit =
  let version = 8 in
    encode_int req_mkt_data oc;
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
    

    (* TODO: combo legs *)
    (*encode_int 0 oc;*)

    (* TODO: undercomp ... *)
    encode_bool false oc;
    
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
