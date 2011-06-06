
type executionFilter = {
  mutable clientId: int;
  mutable acctCode: string;
  mutable time: string;
  mutable ef_symbol: string;
  mutable ef_secType: string;
  mutable ef_exchange: string;
  mutable side: string;
};;

let build_executionFilter = {
  clientId = 0;
  acctCode= "";
  time= "";
  ef_symbol= "";
  ef_secType= "";
  ef_exchange= "";
  side= "";
};;
  
