Require Num.
Require Ord.
Require Bool.

Open StdLib.N.

Definition Ncomparaison x y :=
  if (Neq x y) then Eq else
    (
      if (Nlt x y) then Lt else Gt
    ).

Open TypeClass.Instance.

Definition NOrd :=
  isOrd Ncomparaison.

Close.




Open TypeClass.Instance.

Definition NNum :=
  isNum Nplus Nmultiply Nminus Ndivide.

Close.

Close.

