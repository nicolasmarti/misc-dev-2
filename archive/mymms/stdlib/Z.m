Open StdLib.Z.

Require Ord.
Require Bool.

Definition Zcomparaison x y :=
  if (Zeq x y) then Eq else
    (
      if (Zlt x y) then Lt else Gt
    ).

Open TypeClass.Instance.

Definition ZOrd :=
  isOrd Zcomparaison.

Close.

Require Num.

Open TypeClass.Instance.

Definition ZNum :=
  isNum Zplus Zmultiply Zminus Zdivide.

Close.

Close.
