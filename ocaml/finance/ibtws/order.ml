let customer = 0;;
let firm = 1;;
let unknown = 2;;

let auction_unset = 0;;
let auction_match = 1;;
let auction_improvement = 2;;
let auction_transparent = 3;;

type tagValue = string * string;;

type order = {
  mutable orderId : int64;
  mutable clientId : int64;
  mutable permId : int64;

  mutable oaction : string;
  mutable totalQuantity : int64;
  mutable orderType : string;
  mutable lmtPrice : float;
  mutable auxPrice : float;

  mutable tif : string;
  mutable ocaGroup : string;
  mutable ocaType : int;
  mutable orderRef : string;
  mutable transmit : bool;
  mutable parentId : int64;
  mutable blockOrder : bool;
  mutable sweepToFill : bool;
  mutable displaySize : int;
  mutable triggerMethod : int;
  mutable outsideRth : bool;
  mutable hidden : bool;
  mutable goodAfterTime : string;
  mutable goodTillDate : string;
  mutable rule80A : string;
  mutable allOrNone : bool;
  mutable minQty : int;
  mutable percentOffset : float;
  mutable overridePercentageConstraints : bool;
  mutable trailStopPrice : float;

  mutable faGroup : string;
  mutable faMethod : string;
  mutable faProfile : string;
  mutable faPercentage : string;

  mutable oopenClose : string;
  mutable origin : int;
  mutable oshortSaleSlot : int;
  mutable odesignatedLocation : string;
  mutable oexemptCode : int;
  mutable discretionaryAmt : float;
  mutable eTradeOnly : bool;
  mutable firmQuoteOnly : bool;
  mutable nbboPriceCap : float;

  mutable auctionStrategy: int;
  mutable startingPrice: float;
  mutable stockRefPrice: float;
  mutable odelta: float;

  mutable stockRangeLower: float;
  mutable stockRangeUpper: float;

  mutable volatility: float;
  mutable volatilityType: int;
  mutable deltaNeutralOrderType: string;
  mutable deltaNeutralAuxPrice: float;
  mutable continuousUpdate: bool;
  mutable referencePriceType: int;

  mutable basisPoints: float;
  mutable basisPointsType: int;

  mutable scaleInitLevelSize: int;
  mutable scaleSubsLevelSize: int;
  mutable scalePriceIncrement: float;

  mutable account: string;
  mutable settlingFirm: string;
  mutable clearingAccount: string;
  mutable clearingIntent: string;

  mutable algoStrategy: string;

  mutable algoParams: tagValue list;

  mutable whatIf: bool;

  mutable notHeld: bool;
};;

let build_order () = {
  orderId = Int64.zero;
  clientId = Int64.zero;
  permId = Int64.zero;

  oaction = "";
  totalQuantity = Int64.zero;
  orderType = "";
  lmtPrice = 0.0;
  auxPrice = 0.0;

  tif = "";
  ocaGroup = "";
  ocaType = 0;
  orderRef = "";
  transmit = false;
  parentId = Int64.zero;
  blockOrder = false;
  sweepToFill = false;
  displaySize = 0;
  triggerMethod = 0;
  outsideRth = false;
  hidden = false;
  goodAfterTime = "";
  goodTillDate = "";
  rule80A = "";
  allOrNone = false;
  minQty = 0;
  percentOffset = 0.0;
  overridePercentageConstraints = false;
  trailStopPrice = 0.0;

  faGroup = "";
  faMethod = "";
  faProfile = "";
  faPercentage = "";

  oopenClose = "";
  origin = unknown;
  oshortSaleSlot = 0;
  odesignatedLocation = "";
  oexemptCode = 0;
  discretionaryAmt = 0.0;
  eTradeOnly = false;
  firmQuoteOnly = false;
  nbboPriceCap = 0.0;

  auctionStrategy = auction_unset;
  startingPrice= 0.0;
  stockRefPrice= 0.0;
  odelta= 0.0;

  stockRangeLower= 0.0;
  stockRangeUpper= 0.0;

  volatility= 0.0;
  volatilityType= 0;
  deltaNeutralOrderType= "";
  deltaNeutralAuxPrice= 0.0;
  continuousUpdate= false;
  referencePriceType= 0;

  basisPoints= 0.0;
  basisPointsType= 0;

  scaleInitLevelSize= 0;
  scaleSubsLevelSize= 0;
  scalePriceIncrement= 0.0;

  account= "";
  settlingFirm= "";
  clearingAccount= "";
  clearingIntent= "";

  algoStrategy= "";

  algoParams = [];

  whatIf= false;

  notHeld= false;
};;


type orderState = {
  mutable status: string;

  mutable initMargin: string;
  mutable maintMargin: string;
  mutable equityWithLoan: string;

  mutable commission: float;
  mutable minCommission: float;
  mutable maxCommission: float;
  mutable commissionCurrency: string;

  mutable warningText: string;
};;

let build_orderState () = {
  status= "";

  initMargin= "";
  maintMargin= "";
  equityWithLoan= "";

  commission= 0.0;
  minCommission= 0.0;
  maxCommission= 0.0;
  commissionCurrency= "";

  warningText= "";
};;
  



