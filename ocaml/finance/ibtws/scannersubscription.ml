open Encdec;;
open Contract;;

type scannerSubscription = {
  mutable numberOfRows : int;
  mutable instrument : string;
  mutable locationCode : string;
  mutable scanCode : string;
  mutable abovePrice : float;
  mutable belowPrice : float;
  mutable aboveVolume : int;
  mutable marketCapAbove : float;
  mutable marketCapBelow : float;
  mutable moodyRatingAbove : string;
  mutable moodyRatingBelow : string;
  mutable spRatingAbove : string;
  mutable spRatingBelow : string;
  mutable maturityDateAbove : string;
  mutable maturityDateBelow : string;
  mutable couponRateAbove : float;
  mutable couponRateBelow : float;
  mutable excludeConvertible : bool;
  mutable averageOptionVolumeAbove: int;
  mutable scannerSettingPairs : string;
  mutable stockTypeFilter : string;
};;

let build_scannerSubscription () =
{
  numberOfRows = -1;
  instrument = "";
  locationCode = "";
  scanCode = "";
  abovePrice = dbl_max;
  belowPrice = dbl_max;
  aboveVolume = int_max;
  marketCapAbove = dbl_max;
  marketCapBelow = dbl_max;
  (* Aaa -> I *)
  moodyRatingAbove = "";
  moodyRatingBelow = "";
  (* AAA -> D *)
  spRatingAbove = "";
  spRatingBelow = "";
  maturityDateAbove = "";
  maturityDateBelow = "";
  couponRateAbove = dbl_max;
  couponRateBelow = dbl_max;
  excludeConvertible = false;
  averageOptionVolumeAbove = 0;
  scannerSettingPairs = "";
  stockTypeFilter = "";
};;


type scanData = {
  mutable con : contractDetails;
  mutable rank : int;
  mutable distance : string;
  mutable benchmark : string;
  mutable projection : string;
  mutable legsStr : string;
};;

let build_scanData () = {
  con = build_contractDetails ();
  rank = 0;
  distance = "";
  benchmark = "";
  projection = "";
  legsStr = "";
};;
