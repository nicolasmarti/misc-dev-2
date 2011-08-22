Require Nat.

Open StdLib.Vector.

Inductive vector A : nat -> Type :=
| emptyvector: vector A O
| nextvector: V (n: nat). A -> vector A n -> vector A (S n).
Implicite emptyvector [1].
Implicite nextvector [2].

Recursive appvector A n1 n2 (l1: vector A n1) (l2: vector A n2) [3] : list A (natplus n1 n2) := 
   match l1 with
     | emptyvector ==> l2
     | nextvector hd1 tl1 ==>
        nextvector hd1 (appvector _ _ _ tl1 l2).
Implicite appvector [3].

Close.