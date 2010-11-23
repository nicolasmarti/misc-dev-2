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

let test2 oc =   
  let c = build_contract () in

    c.symbol <- "STAN";
    c.secType <- "STK";
    c.exchange <- "SMART";
    c.primaryExchange <- "LSE";
    c.currency <- "GBP";

    printf "requesting market data\n";
    reqMktData !currId c "100,101,104,105,106,107,125,165,225,221,236,258,291" false oc;
    flush stdout;
    sleep 10;
    printf "cancel market data\n";
    cancelMktData !currId oc;
    flush stdout
;;

let test3 oc =   
  let c = build_contract () in

    c.symbol <- "STAN";
    c.secType <- "STK";
    c.exchange <- "SMART";
    c.primaryExchange <- "LSE";
    c.currency <- "GBP";

    printf "requesting market depth\n";
    reqMktDepth !currId c 1 oc;
    flush stdout;
    sleep 10;
    printf "cancel market depth\n";
    cancelMktDepth !currId oc;
    flush stdout
;;

let test4 oc =
  let c = build_contract () in

    c.symbol <- "GS";
    c.secType <- "STK";
    c.exchange <- "SMART";
    c.primaryExchange <- "NYSE";
    c.currency <- "USD";

    printf "requesting historical data\n";
    reqHistoricalData !currId c "20101112 12:00:00" "3600 S" "5 mins" "TRADES" 0 1 oc;
    flush stdout;
    sleep 10;
    printf "cancel historical data\n";
    cancelHistoricalData !currId oc;
    flush stdout
;;

let test5 oc =
  let c = build_contract () in

    c.symbol <- "GS";
    c.secType <- "STK";
    c.exchange <- "SMART";
    c.primaryExchange <- "NYSE";
    c.currency <- "USD";

    printf "requesting real time bars\n";
    reqRealTimeBars !currId c 5 "TRADES" 0 oc;
    flush stdout;
    sleep 20;
    printf "cancel real time bars\n";
    cancelRealTimeBars !currId oc;
    flush stdout
;;

Random.self_init ();;

let clientId = (Random.int 65000);;

printf "clientId = %d\n" clientId;;

let (ic, oc) = tws_connect "127.0.0.1" 7496 clientId;;

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

shutdown_connection ic;;

