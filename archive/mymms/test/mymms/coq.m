Inductive nat: Type :=
| O: nat
| S: nat -> nat.

Recursive T A B (n: nat) [2] : Type :=
   match n with
     | O ==> A
     | S n ==> (B -> T A B n).

Recursive fold2 A B (f: A -> B -> A) n b [3] : V (H: T A B n). T A B n :=
     match n with
       | O ==> \ (x: A). f x b
       | S n ==> 
                \ (g: T A B (S n)). \ (y2: B). 
                          fold2 A B f n b (g y2).

Recursive fold A B (f: A -> B -> A) (a: A) n [4] : T A B n :=
     match n with
       | O ==> a
       | S n ==> \ (x: B). fold2 A B f n x (fold A B f a n).

Require Float.

Check Float.

Check (\ (x y: Float). x + y).


Definition sum : V (n: nat). T Float Float n :=
     fold Float Float (\ (x y: Float). x + y) 0.0.

Require N.

Show NFoldLeft.

Definition N2nat n := NFoldLeft _ 0 n 1 (\ acc x. S acc) O.

Simpl (N2nat 6).

Definition msum n := sum (N2nat n).

Check msum.

Simpl (

      msum
	5
	9.8
	8.92
	7.678
	9 8
	45
).