Open StdLib.Nat.

Inductive nat :=
| O: nat
| S: nat -> nat.

Require Ord.

Recursive natcompare x y [0, 1] :=
   match (pair x y) with
     | pair O O ==> Eq
     | pair (S x) O ==> Gt
     | pair O (S y) ==> Lt
     | pair (S x) (S y) ==> natcompare x y.

Open TypeClass.Instance.

Definition natOrd :=
  isOrd natcompare.

Close.


Recursive natplus x y [0] :=
  match x with
    | O ==> y
    | S x ==> S (natplus x y).

Recursive natmul x y [0] :=
  match x with
    | O ==> O
    | S x ==> natplus y (natmul x y).

Require Prod.

Recursive natmin x y [0] :=
  match pair x y with
    | pair O _ ==> O
    | pair _ O ==> x
    | pair (S x) (S y) ==> natmin x y.

Recursive natdiv x y :=
  match natcompare x y with
    | Eq ==> S O
    | Lt ==> O
    | GT ==> S (natdiv (natmin x y) y).

Require Num.

Open TypeClass.Instance.

Definition NatNum :=
  isNum natplus natmul natmin natdiv.

Close.




Close.