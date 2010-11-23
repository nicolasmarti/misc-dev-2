

type legOpenClose =
  | SAME_POS
  | OPEN_POS
  | CLOSE_POS
  | UNKNOWN_POS
;;

type comboLeg = {
  mutable conId : int;
  mutable ratio : float;
  mutable action : string;
  mutable openClose : legOpenClose;
  mutable shortSaleSlot : int;
  mutable designatedLocation : string;
};;

let build_comboLeg () =
  { conId = 0;
    ratio = 0.0;
    action = "";
    openClose = UNKNOWN_POS;
    shortSaleSlot = 0;
    designatedLocation = ""
  }
;;

type underComp = {
  mutable conId: int;
  mutable delta: float;
  mutable price: float;  
};;

let build_underComp () =
  { conId = 0;
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
  mutable comboLegsDescrip: string;
  mutable comboLegs: comboLeg list;
  mutable undercomp: underComp;
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
    comboLegsDescrip = "";
    comboLegs = [];
    undercomp = build_underComp ()
  }
