Open StdLib.Bool.

Inductive bool :=
| true: bool
| false: bool.

Definition band x y :=
  match x with
    | false ==> false
    | _ ==> y.

Definition bor x y :=
  match x with
    | true ==> true
    | _ ==> y.

Definition bneg x :=
  match x with
    | true ==> false
    | _ ==> true.

Definition bimpl x y :=
  match x with
    | false ==> true
    | true ==> y.

Close.
