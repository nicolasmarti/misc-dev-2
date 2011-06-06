
type executionFilter = {
  mutable ef_clientId: int;
  mutable acctCode: string;
  mutable ef_time: string;
  mutable ef_symbol: string;
  mutable ef_secType: string;
  mutable ef_exchange: string;
  mutable ef_side: string;
};;

let build_executionFilter = {
  ef_clientId = 0;
  acctCode= "";
  ef_time= "";
  ef_symbol= "";
  ef_secType= "";
  ef_exchange= "";
  ef_side= "";
};;
  
type execution = {
  mutable execId: string;
  mutable ex_time: string;
  mutable acctNumber: string;
  mutable ex_exchange: string;
  mutable ex_side: string;
  mutable shares: int;
  mutable ex_price: float;
  mutable ex_permId: int;
  mutable ex_clientId: int;
  mutable ex_orderId: int;
  mutable liquidation: int;
  mutable cumQty: int;
  mutable avgPrice: float;
};;

let build_execution () = {
  execId = "";
  ex_time = "";
  acctNumber = "";
  ex_exchange = "";
  ex_side = "";
  shares = 0;
  ex_price = 0.0;
  ex_permId = 0;
  ex_clientId = 0;
  ex_orderId = 0;
  liquidation = 0;
  cumQty = 0;
  avgPrice = 0.0;
};;





