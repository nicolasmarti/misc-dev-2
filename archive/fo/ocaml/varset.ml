open Set;;
open String;;

module OrderedVar =
  struct
    type t = string
    let compare x y = String.compare x y
  end;;

module VarSet = Set.Make(OrderedVar);;

let (+++) s1 s2 = VarSet.union s1 s2;;

let (++) e s2 = VarSet.union (VarSet.singleton e) s2;;
