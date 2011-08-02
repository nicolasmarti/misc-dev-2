Require N.
Require Prod.
Require Bool.

Inductive PL :=
| PLTrue: PL
| PLFalse: PL
| PLVar: N -> PL
| PLNeg: PL -> PL
| PLAnd: PL -> PL -> PL
| PLOr: PL -> PL -> PL
| PLImpl: PL -> PL -> PL
| PLIff:  PL -> PL -> PL.

Recursive PLcomparaison x y [0, 1] :=
 match pair x y with
   | pair PLTrue PLTrue ==> true
   | pair PLFalse PLFalse ==> true
   | pair (PLVar v1) (PLVar v2) ==> v1 == v2
   | pair (PLNeg p1) (PLNeg p2) ==> PLcomparaison p1 p2
   | pair (PLAnd p11 p12) (PLAnd p21 p22) ==> (PLcomparaison p11 p21) && (PLcomparaison p12 p22)
   | pair (PLOr p11 p12) (PLOr p21 p22) ==> (PLcomparaison p11 p21) && (PLcomparaison p12 p22)
   | pair (PLImpl p11 p12) (PLImpl p21 p22) ==> (PLcomparaison p11 p21) && (PLcomparaison p12 p22)
   | pair (PLIff p11 p12) (PLIff p21 p22) ==> (PLcomparaison p11 p21) && (PLcomparaison p12 p22)
   | _ ==> false.

Open TypeClass.Instance.

Definition PLEq :=
  isEqDec PLcomparaison.

Close.

Require Logic.

Recursive PLsemantics f interp [0] :=
  match f with
    | PLTrue ==> true
    | PLFalse ==> false
    | PLVar v ==> interp v
    | PLNeg f1 ==> bneg (PLsemantics f1 interp)
    | PLAnd f1 f2 ==> band (PLsemantics f1 interp) (PLsemantics f2 interp)
    | PLOr f1 f2 ==> bor (PLsemantics f1 interp) (PLsemantics f2 interp)
    | PLImpl f1 f2 ==> bimpl (PLsemantics f1 interp) (PLsemantics f2 interp)
    | PLIff f1 f2 ==> band (bimpl (PLsemantics f1 interp) (PLsemantics f2 interp))
      	       	      	   (bimpl (PLsemantics f2 interp) (PLsemantics f1 interp))
.

Simpl (PLsemantics PLTrue (\ x -> true)).

Inductive PLproof1 : PL -> Type :=
| proof1PLTrue: PLproof1 PLTrue
| proof1PLImpl: V P1 P2. PLproof1 (PLOr (PLNeg P1) (P2)) -> PLproof1 (PLImpl P1 P2)
| proof1PLIff: V P1 P2. PLproof1 (PLAnd (PLImpl P1 P2) (PLImpl P2 P1)) -> PLproof1 (PLIff P1 P2)
| proof1PLAnd: V P1 P2. PLproof1 P1 -> PLproof1 P2 -> PLproof1 (PLAnd P1 P2)
| proof1PLOr1: V P1 P2. PLproof1 P1 -> PLproof1 (PLOr P1 P2)
| proof1PLOr2: V P1 P2. PLproof1 P2 -> PLproof1 (PLOr P1 P2)
| proof1PLEM: V P1. PLproof1 P1 -> PLproof1 (PLNeg P1) -> PLproof1 PLFalse
| proof1Absurd: PLproof1 PLFalse -> V P. PLproof1 P.



