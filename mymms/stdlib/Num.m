Open StdLib.Num.

Require Bool.

Open TypeClass.Definition.

Inductive Num A :=
| isNum: 
   V (plus: A -> A -> A)
     (mult: A -> A -> A)
     (minus: A -> A -> A)
     (divide: A -> A -> A).
     	      Num A.
Implicite isNum [1].

Close.

Definition NumPlus A (H: Num A) :=
  match H with
    | isNum p _ _ _ ==> p.
Implicite NumPlus [2].
Overload plus with @NumPlus [2].

Definition NumMult A (H: Num A) :=
  match H with
    | isNum _ m _ _ ==> m.
Implicite NumMult [2].
Overload mult with @NumMult [2].

Definition NumMinus A (H: Num A) :=
  match H with
    | isNum _ _ m _ ==> m.
Implicite NumMinus [2].
Overload minus with @NumMinus [2].

Definition NumDivide A (H: Num A) :=
  match H with
    | isNum _ _ _ d ==> d.
Implicite NumDivide [2].
Overload divide with @NumDivide [2].

Close.
