Inductive Bool :=
| True: Bool
| False: Bool.

Inductive list (A: Type) :=
| nil: list A
| cons: A -> (list A) -> list A.

Inductive nat :=
| O: nat
| S: nat -> nat.

Recursive plus (a: nat) (b: nat) :=
 match a with
   | O ==> b
   | S a ==> S (plus a b).

Recursive mult (a: nat) (b: nat) :=
 match a with
   | O ==> O
   | S a ==> plus b (mult a b).

Recursive power (a: nat) (b: nat) :=
 match a with
   | O ==> (S O)
   | S a ==> mult b (power a b).

Recursive length {A: Type} (l: list A) : _ :=
  match l with
    | nil _ ==> O
    | cons _ hd tl ==> S (length tl).

Recursive app {A: Type} (l1: list A) (l2: list A) : _ :=
  match l1 with
    | nil _ ==> l2
    | cons _ hd tl ==> cons _ hd (app tl l2).

Recursive revapp {A: Type} (l1: list A) (l2: list A) : _ :=
  match l1 with
    | nil _ ==> l2
    | cons _ hd tl ==> revapp tl (cons _ hd l2).

Definition rev {A: Type} (l: list A) : _ :=
  revapp l (nil _).

Recursive map {A: Type} {B: Type} (f: A -> B) (l: list A) : _ :=
   match l with
     | nil _ ==> nil _
     | cons _ hd tl ==> cons _ (f hd) (map f tl).

Recursive iota (n: nat) :=
   match n with
     | O ==> nil _
     | S x ==> cons _ n (iota x).
