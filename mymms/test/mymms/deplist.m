Require Bool.
Require Nat.

Inductive list A : nat -> Type :=
| nil: list A O
| conc: V n. A -> list A n -> list A (S n).
Implicite nil [1].
Implicite conc [2].

Definition f1 := (
      \ A n (l: list A (S n)).
      	let (conc _ _) := l in true
).

Recursive app A n1 n2 (l1: list A n1) (l2: list A n2) [3] : list A (natplus n1 n2) := 
   match l1 with
     | nil ==> l2
     | conc e l1 ==>
        conc e (app _ _ _ l1 l2).
Implicite app [3].

Lemma l1: list Type (S O).
      apply @conc.
      apply Type.
      apply @nil.

Simpl (app l l).
Interp (app l l).

Recursive app_interm A n1 n2 (l1: list A n1) (l2: list A n2) [3] : list A (natplus n1 n2) :=
   match l1 with
     | nil ==> l2
     | conc e l1 ==>
         app_interm _ _ _ l1 (conc e l2).
