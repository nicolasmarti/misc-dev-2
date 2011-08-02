Open StdLib.Q.

Require Bool.
Require Ord.

Definition Qcomparaison x y :=
  if (Qeq x y) then Eq else
    (
      if (Qlt x y) then Lt else Gt
    ).

Open TypeClass.Instance.

Definition QOrd :=
  isOrd Qcomparaison.

Close.


Require Num.

Open TypeClass.Instance.

Definition QNum :=
  isNum Qplus Qmultiply Qminus Qdivide.

Close.

Close.
