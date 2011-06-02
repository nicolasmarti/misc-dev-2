open Unix;;
open Printf;;
open Pervasives;;
open Encdec;;

let client_version = 48;;

let server_version = ref 0;;

let tws_connect ip port clientId =

  let addr = (ADDR_INET (inet_addr_of_string ip, port)) in

  let (ic, oc) = open_connection addr in

    (*
    printf "connected ...\n";
    flush stdout;
    *)

    (* need to send the client version *)
    (* EClientSocketBase::onConnectBase *)
    encode_int client_version oc;
    flush oc;

    (* grab the server version *)
    (* EClientSocketBase::processConnectAck *)
    server_version := decode_int ic;
    printf "server_version = %d\n" !server_version;
    if !server_version >= 20 then (
	(*printf "server_version >= 20\n";*)
      let twstime = decode_string ic in
      printf "twstime = %s\n" twstime
    ) else 
	(*printf "server_version < 20\n";*)
      ();
    
    if !server_version >= 3 then (
      (*printf "server_version >= 3\n";*)
      encode_int clientId oc;
      flush oc;
      
    ) else 
	(*printf "server_version < 20\n";*)
      ();
    
    flush stdout;
    (ic, oc)
;;


