Open StdLib.Showable.

Open TypeClass.Definition.

Inductive Showable A :=
| isShowable: 
   V (show: A -> String).
     	      Showable A.
Implicite isShowable [1].

Close.

Definition show A (H: Showable A) :=
  match H with
    | isShowable s ==> s.
Implicite show [2].

Require N.

Open TypeClass.Instance.
Definition NShowable :=
  isShowable StdLib.N.NtoString.

Definition FloatShowable :=
  isShowable StdLib.float.FloatToString.

Close.



Close.