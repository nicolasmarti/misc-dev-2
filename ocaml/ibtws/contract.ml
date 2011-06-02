

type legOpenClose =
  | SAME_POS
  | OPEN_POS
  | CLOSE_POS
  | UNKNOWN_POS
;;

type comboLeg = {
  mutable cl_conId : int;
  mutable ratio : float;
  mutable action : string;
  mutable cl_exchange : string;
  mutable openClose : legOpenClose;
  mutable shortSaleSlot : int;
  mutable designatedLocation : string;
  mutable exemptCode : int;
};;

let build_comboLeg () =
  { cl_conId = 0;
    ratio = 0.0;
    action = "";
    cl_exchange = "";
    openClose = UNKNOWN_POS;
    shortSaleSlot = 0;
    designatedLocation = "";
    exemptCode = 0
  }
;;

type underComp = {
  mutable uc_conId: int;
  mutable delta: float;
  mutable price: float;  
};;

let build_underComp () =
  { uc_conId = 0;
    delta = 0.0;
    price = 0.0
  }

type contract = {
  mutable conId: int;
  mutable symbol: string;
  mutable secType: string;
  mutable expiry: string;
  mutable strike: float;
  mutable right: string;
  mutable multiplier: string;
  mutable exchange: string;
  mutable primaryExchange: string;
  mutable currency: string;
  mutable localSymbol: string;
  mutable includeExpired: bool;
  mutable secIdType: string;
  mutable secId: string;
  mutable comboLegsDescrip: string;
  mutable comboLegs: comboLeg list;
  mutable undercomp: underComp option;
};;

let build_contract () =
  { conId = 0;
    symbol = "";
    secType = "";
    expiry = "";
    strike = 0.0;
    right = "";
    multiplier = "";
    exchange = "";
    primaryExchange = "";
    currency = "";
    localSymbol = "";
    includeExpired = false;
    secIdType = "";
    secId = "";
    comboLegsDescrip = "";
    comboLegs = [];
    undercomp = None
  }
