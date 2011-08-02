Inductive nat: Type :=
| O: nat
| S: nat -> nat.

Recursive plus x y [0] :=
  match x with
    | O ==> y
    | S x ==> S (plus x y).

Inductive list A :=
| nil: list A
| conc: A -> list A -> list A.
Implicite nil [1].
Implicite conc [1].

Recursive altlist A (l1: list A) l2 [1,2] :=
  match l1 with
    | nil ==> l2
    | conc hd1 tl1 ==> conc hd1 (altlist _ l2 tl1).
Implicite altlist [1].

Simpl (

      altlist
      (conc 0 (conc 2 (conc 4 nil)))
      (conc 1 (conc 3 (conc 5 nil)))
).

Require List.
