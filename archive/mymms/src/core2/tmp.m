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

Definition test2 := mult (S (S O)) (S (S O)).

Definition l1 := iota test2.

Definition l2 := map (\ x -> x) l1.


Definition t (x: nat) := plus (S x) O.

Inductive Maybe (A: Type) :=
| Nothing: Maybe A
| Just: A -> Maybe A.

Inductive Prod (A: Type) (B: Type) :=
| pair: A -> B -> Prod A B.

Inductive Bool :=
| True: Bool
| False: Bool.

Definition tt (a: nat) (b: Maybe nat) : _ :=
  match pair _ _ a b with
    | pair _ _ O (Nothing _) ==> True
    | _ ==> True.



******************************
let f = (\ {x: Type} (y: x) -> y) in 
let x = Type in 
let y = x in
f x

\ (f: _ -> Type)  -> let x = Type in f x

let f = (\ {x: Type} (y: x) -> y) in 
let x = Type in 
let y = x in
(f x)


Inductive list (A: Type) : Type :=
| nil: list A
| cons: A -> list A -> list A

Inductive nat : Type :=
| O: nat
| S: nat -> nat

Recursive f (x: Type) : Type := f x

Definition f (A: Type) (x: A) : _ := x.

Recursive f (x: Type) : _ := f x.

Inductive list (A: Type) : Type :=
| nil: list A
| cons: A -> list A -> list A.
 
Definition t : _ := S O.

Definition t2 (x: _): _ := 
   match S x with
     | O ==> O
     | S _ ==> S O.

Inductive vector (A: Type) : Type :=
| niln: list A O.
| consn: V [n: nat]. A -> list A n -> list A (S n).

Inductive vector (A: Type) : nat -> Type :=
| niln: vector A O
| consn: V (n: nat). A -> vector A n -> vector A (S n).

Inductive list (A: Type) :=
| nil: list A
| cons: A -> list A -> list A.

Inductive list (A: Type) :=
| nil: list A
| cons: A -> list A -> list A.

Inductive vector (A: Type) : nat -> Type :=
| niln: vector A O
| consn: V (n: nat). A -> vector A n -> vector A (S n).

Inductive vector (A: Type) : nat -> Type :=
| niln: vector A O
| consn: V (n: nat). A -> vector A n -> vector A (S n).

Inductive nat : Type :=
| O: nat
| S: nat -> nat.
Inductive list (A: Type) :=
| nil: list A
| cons: A -> list A -> list A.
Inductive vector (A: Type) : nat -> Type :=
| niln: vector A O
| consn: V (n: nat). A -> (vector A n) -> vector A (S n).

Definition t2 (x: _): _ := 
   match S x with
     | O ==> O
     | S _ ==> S O.
Recursive t3 (x: _) := S (t3 (S x)).
Inductive nat : Type :=
| O: nat
| S: nat -> nat.
Inductive list (A: Type) :=
| nil: list A
| cons: A -> list A -> list A.
Inductive vector (A: Type) : [nat] -> Type :=
| niln: vector A O
| consn: V (n: nat). A -> (vector A n) -> vector A (S n).
Definition test := vector.
Definition test2 (x: Type) [y: x] := x.
Definition test3 := test2 Type Type.
Definition test4 (x: Type) [y: x] (z: x):= x.
Definition test5 := test4 Type Type Type.
Inductive vector (A: Type) : [nat] -> Type :=
| niln: vector A O
| consn: V [n: nat]. A -> (vector A n) -> vector A (S n).
Definition vector1 := consn _ O (S O) (niln _).
Definition v : vector nat O := niln _.
Inductive vector (A: Type) : [nat] -> Type :=
| niln: vector A O
| consn: V (n: nat). A -> (vector A n) -> vector A (S n).
Definition vector1 := consn _ O (S O) (niln _).
Inductive nat : Type :=
| O: nat
| S: nat -> nat.
Inductive bool : Type :=
| true: bool
| false: bool.
Definition t := \ f x ->
   match f x with
     | O ==> S x
     | S x ==> S (S x).
Inductive list (A: Type) :=
| nil: list A
| cons: A -> list A -> list A.
Inductive vector (A: Type) : nat -> Type :=
| niln: vector A O
| consn: V [n: nat]. A -> (vector A n) -> vector A (S n).
Definition vector1 := consn _ O (S O) (niln _).
Definition f {A: Type} (a: A) := a.
Definition test := f (S O).
Definition f2 [A: Type] (a: A) := a.
Definition test2 := f2 _ (S O).
Recursive length (A: Type) (l: list A) : _ :=
   match l with
     | nil _ ==> O
     | cons _ hd tl ==> S (length _ tl).
Recursive length (A: Type) (l: list A) : _ :=
   match l with
     | nil _ ==> O
     | cons _ hd tl ==> S (length _ tl).

Definition d := \ l ->
   match l with
     | (nil _) ==> nil _
     | (cons _ O tl) ==> (cons _ O tl).

Recursive length3 (A: Type) (l: list A) : _ := l.
Definition length3 (l: list _) : list nat := l.
Definition t2 : list nat := cons a b c.

Recursive length (A: Type) (l: list A) : _ :=
   match l with
     | (nil _) ==> O
     | (cons _ hd tl) ==> S (length _ tl).
Recursive length (A: Type) (l: list A) : _ :=
   match l with
     | (nil _) ==> O
     | (cons _ hd tl) ==> S (length _ tl).
Inductive nat : Type :=
| O: nat
| S: nat -> nat.
Inductive list (A: Type) :=
| nil: list A
| cons: A -> (list A) -> list A.
Recursive length (A: Type) (l: list A) : _ :=
   match l with
     | (nil _) ==> O
     | (cons _ hd tl) ==> S (length _ tl).
Recursive length (A: Type) (l: list A) : _ :=
   match l with
     | (nil _) ==> O
     | (cons _ hd tl) ==> S (length _ tl).
Inductive eq (A: Type) (a: A) : A -> Type :=
| eqrefl: eq A a a.
Inductive list (A: Type) :=
| nil: list A
| cons: A -> (list A) -> list A.
Definition length3 (A: Type) (l: list A) : _ := l.
Recursive length4 (A: Type) (l: list A) : _ := l.
Inductive nat : Type :=
| O: nat
| S: nat -> nat.
Recursive plus (a: nat) (b: nat) : _ :=
 match a with
   | O ==> b
   | S a ==> S (plus a b).
Recursive mult (a: nat) (b: nat) : _ :=
 match a with
   | O ==> O
   | S a ==> plus b (mult a b).
Recursive power (a: nat) (b: nat) : _ :=
 match a with
   | O ==> (S O)
   | S a ==> mult b (power a b).
Definition test := (\ A (x: A) -> x) _ O.
Definition test2 := mult (S (S O)) (S (S O)).
Definition test3 := mult (S (S (S O))) (power (S (S O)) (S (S (S O)))).


Definition caca := \ (a: nat) -> 
                      let v = S a in 
		      match v with   
		        | O ==> O 
		        | S x ==> S x.
Recursive T (A: Type) (B: Type) (n: nat) : Type :=
   match n with
     | O ==> A
     | S n ==> (B -> (T A B n)).
Definition caca := \ (A: Type) (a: A) -> a.
Recursive fold2 (A: Type) (B: Type) (f: A -> B -> A) (n: nat) (b: B) : V (H: T A B n). T A B n :=
     match n with
       | O ==> \ (x: A) -> f x b
       | S n ==> \ (g: T A B (S n)) (y2: B) -> (fold2 A B f n b (g y2)).



Definition test := (\ A (x: A) -> x) _ O.

Definition test2 := mult (S (S O)) (S (S O)).

Inductive list (A: Type) :=
| nil: list A
| cons: A -> (list A) -> list A.


Definition l1 := iota (S (S (S O))).

Definition f := (\ x -> x) O.

Definition l2 : list nat := map (\ x -> x) l1.


Inductive Obs : Type -> Type :=
| con: V (A: Type). A -> Obs A
| app: V (A: Type) (B: Type). (Obs (A -> B)) -> (Obs A) -> Obs B.

Recursive t {A: Type} (o: Obs A) : A :=
  match o with
    | con A a ==> a
    | app A B f a ==> (t f) (t a)
.

