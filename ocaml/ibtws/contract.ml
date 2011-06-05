

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
;;

type contractDetails =
{
   mutable summary : contract;
   mutable marketName : string;
   mutable tradingClass : string;
   mutable minTick : float;
   mutable orderTypes : string;
   mutable validExchanges : string;
   mutable priceMagnifier : float;
   mutable underConId : int;
   mutable longName : string;
   mutable contractMonth : string;
   mutable industry : string;
   mutable category : string;
   mutable subcategory : string;
   mutable timeZoneId : string;
   mutable tradingHours : string;
   mutable liquidHours : string;

   mutable cusip : string;
   mutable ratings : string;
   mutable descAppend : string;
   mutable bondType : string;
   mutable couponType : string;
   mutable callable : bool;
   mutable putable : bool;
   mutable coupon : float;
   mutable convertible : bool;
   mutable maturity : string;
   mutable issueDate : string;
   mutable nextOptionDate : string;
   mutable nextOptionType : string;
   mutable nextOptionPartial : bool;
   mutable notes : string;
};;

let build_contractDetails () = {
  summary = build_contract ();
  marketName = "";
  tradingClass = "";
  minTick = 0.0;
  orderTypes = "";
  validExchanges = "";
  priceMagnifier = 0.0;
  underConId = 0;
  longName = "";
  contractMonth = "";
  industry = "";
  category = "";
  subcategory = "";
  timeZoneId = "";
  tradingHours = "";
  liquidHours = "";

  cusip = "";
  ratings = "";
  descAppend = "";
  bondType = "";
  couponType = "";
  callable = false;
  putable = false;
  coupon = 0.0;
  convertible = false;
  maturity = "";
  issueDate = "";
  nextOptionDate = "";
  nextOptionType = "";
  nextOptionPartial = false;
  notes = "";
};;












