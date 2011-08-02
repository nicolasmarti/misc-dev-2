Open StdLib.Order.

Require Bool.
Require Prod.
Require Eq.

Inductive compare :=
| Eq: compare
| Lt: compare
| Gt: compare.

Definition compare_beq x y :=
  match pair x y with
    | pair Eq Eq ==> true
    | pair Lt Lt ==> true
    | pair Gt Gt ==> true
    | _ ==> false.

Open TypeClass.Definition.

Inductive Ord A :=
| isOrd:
    V (comparaison: A -> A -> compare). Ord A.
Implicite isOrd [1].

Close.

Definition comparaison A (H: Ord A) :=
  match H with
    | isOrd f ==> f.
Implicite comparaison [1].

Definition OrdEqual A (H: Ord A) (x y: A) :=
  let f := comparaison H in
  compare_beq (f x y) Eq.
Implicite OrdEqual [2].
Overload equal with @OrdEqual [2].

Definition OrdLt A (H: Ord A) (x y: A) :=
  let f := comparaison H in
  compare_beq (f x y) Lt.
Implicite OrdLt [2].
Overload lt with @OrdLt [2].

Definition OrdLte A (H: Ord A) (x y: A) :=
  let f := comparaison H in
  (compare_beq (f x y) Lt) || (compare_beq (f x y) Eq).
Implicite OrdLte [2].
Overload lte with @OrdLte [2].

Definition OrdGt A (H: Ord A) (x y: A) :=
  let f := comparaison H in
  compare_beq (f x y) Gt.
Implicite OrdGt [2].
Overload gt with @OrdGt [2].

Definition OrdGte A (H: Ord A) (x y: A) :=
  let f := comparaison H in
  (compare_beq (f x y) Gt) || (compare_beq (f x y) Eq).
Implicite OrdGte [2].
Overload gte with @OrdGte [2].

Definition max A (H: Ord A) (a1 a2: A) :=
   if (OrdLt a1 a2) then a2 else a1.
Implicite max [2].

Definition min A (H: Ord A) (a1 a2: A) :=
   if (OrdLt a1 a2) then a1 else a2.
Implicite min [2].

Definition fromOrd2EqDec A (H: Ord A) : EqDec A :=
   isEqDec (@OrdEqual A H).

Close.
