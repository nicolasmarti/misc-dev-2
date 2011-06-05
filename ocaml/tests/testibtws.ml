open Unix;;
open Printf;;
open Pervasives;;
open Connect;;
open Req;;
open Recv;;
open Contract;;
open Thread;;

open Random;;

let recv_loop ic =
  while true do
    processMsg ic;
    flush stdout;    
  done
;;

let test1 oc = 
  printf "requesting next id\n";
  reqIds 1 oc;
  flush stdout;
  sleep 5
;;

let gs_contract = 
  let c = build_contract () in
  c.symbol <- "GS";
  c.secType <- "STK";
  c.exchange <- "SMART";
  c.primaryExchange <- "NYSE";
  c.currency <- "USD";
  c
;;

let msft_contract = 
  let c = build_contract () in
  c.symbol <- "MSFT";
  c.secType <- "STK";
  c.exchange <- "SMART";
  c.primaryExchange <- "NASDAQ";
  c.currency <- "USD";
  c
;;

let stan_contract = 
  let c = build_contract () in
  c.symbol <- "STAN";
  c.secType <- "STK";
  c.exchange <- "SMART";
  c.primaryExchange <- "LSE";
  c.currency <- "GBP";
  c
;;

let test2 oc =   
    printf "requesting market data\n";
    reqMktData !currId gs_contract "100,101,104,105,106,107,125,165,225,221,236,258,291" false oc;
    flush stdout;
    sleep 10;
    printf "cancel market data\n";
    cancelMktData !currId oc;
    flush stdout
;;

let test3 oc =   
    printf "requesting market depth\n";
    reqMktDepth !currId gs_contract 1 oc;
    flush stdout;
    sleep 10;
    printf "cancel market depth\n";
    cancelMktDepth !currId oc;
    flush stdout
;;

let test4 oc =
    printf "requesting historical data\n";

    let mtime = gmtime (time ()) in
    let date = String.concat " " [
      String.concat "" [string_of_int (mtime.tm_year + 1900); 
			String.concat "" [if (mtime.tm_mon + 1 < 10) then "0" else ""; string_of_int (mtime.tm_mon + 1)]; 
			String.concat "" [if (mtime.tm_mday < 10) then "0" else ""; string_of_int mtime.tm_mday]
		       ];
      String.concat ":" [String.concat "" [if (mtime.tm_hour - 1 < 10) then "0" else ""; string_of_int (mtime.tm_hour - 1)]; 
			 String.concat "" [if (mtime.tm_min < 10) then "0" else ""; string_of_int mtime.tm_min]; 
			 String.concat "" [if (mtime.tm_sec < 10) then "0" else ""; string_of_int mtime.tm_sec]
			]
    ] in

    printf "date = %s" date;

    reqHistoricalData !currId gs_contract date "3600 S" "5 mins" "TRADES" 0 1 oc;
    flush stdout;
    sleep 10;
    (*printf "cancel historical data\n";*)
    (*cancelHistoricalData !currId oc;*)
    flush stdout
;;

let test5 oc =
    printf "requesting real time bars\n";
    reqRealTimeBars !currId gs_contract 5 "MIDPOINT" 0 oc;
    flush stdout;
    sleep 20;
    printf "cancel real time bars\n";
    cancelRealTimeBars !currId oc;
    flush stdout
;;

let test6 oc =
    printf "requesting scanner parameters\n";
    reqScannerParameters oc;
    flush stdout;
    sleep 20;
    flush stdout;
;;

Random.self_init ();;

let clientId = (Random.int 65000);;

printf "clientId = %d\n" clientId;;

let (ic, oc) = tws_connect "192.168.11.5" 7496 clientId;;

let t = Thread.create recv_loop ic;;

test1 oc;;

test2 oc;;
currId := !currId + 1;;

test3 oc;;
currId := !currId + 1;;

test4 oc;;
currId := !currId + 1;;

test5 oc;;
currId := !currId + 1;;

test6 oc;;

shutdown_connection ic;;

