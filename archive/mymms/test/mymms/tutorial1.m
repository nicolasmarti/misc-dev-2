Inductive nat : Type :=
| O: nat
| S: nat -> nat.

Check natinduc.

Recursive natplus (x y: nat) [0] : nat :=
  match x with
    | O ==> y
    | S x ==> S (natplus x y).

Recursive natmul x y [0] :=
  match x with
    | O ==> O
    | S x ==> natplus y (natmul x y).

Check natmul.

Inductive list (A: Type) : Type :=
| nil: list A
| cons: A -> list A -> list A.

Check (cons nat O (cons nat O (nil nat))).

Check (cons _ O (cons _ O (nil _))).

Implicite cons [1].
Implicite nil [1].

Check (cons O (cons O nil)).

Check nil.

Check @nil.

Recursive map A B (f: A -> B) (l: list A) [3] :=
   match l with
     | nil ==> nil
     | cons hd tl ==> cons (f hd) (map _ _ f tl).
Implicite map [2].

Recursive foldl A B (f: A -> B -> A) a l [4] :=
   match l with
     | nil ==> a
     | cons hd tl ==>
       	     foldl _ _ f (f a hd) tl .
Implicite foldl [2].

Recursive foldr A B (f: B -> A -> A) a l [4] :=
   match l with
     | nil ==> a
     | cons hd tl ==>
       	     f hd (foldr _ _ f a tl).
Implicite foldr [2].

Recursive intercalate A a (l: list A) [2] :=
  match l with
    | cons hd1 (cons hd2 tl) ==> cons hd1 (cons a (intercalate _ a (cons hd2 tl)))
    | _ ==> l.
Implicite intercalate [1].

Recursive mixlist A (l1 l2: list A) [1, 2] :=
  match l1 with
    | nil ==> l2
    | cons hd1 tl1 ==>
      	   cons hd1 (mixlist _ l2 tl1).

Inductive listn (A: Type) : nat -> Type :=
| niln: listn A O
| consn: V (n: nat). A -> listn A n -> listn A (S n).

Implicite consn [1].
Implicite niln [1].

Recursive appendn A n1 n2 (l1: listn A n1) (l2: listn A n2) [3] : listn A (natplus n1 n2) :=
   match l1 with
     | niln ==> l2
     | consn n1 a l1 ==> consn _ a (appendn _ _ _ l1 l2).

Implicite appendn [3].

Recursive revn A n (l: listn A n) [2] : listn A n :=
   match l with
     | niln ==> niln
     | consn n e l ==> appendn (revn _ _ l) (consn _ e niln).

Definition fct A n (l: listn A (S n)) := let consn _ e l := l in e.

Inductive eq A (a: A) : A -> Type :=
| eqrefl: eq A a a.

Lemma congruence_eq: V (A: Type) (a b: A) (H: eq A a b) (P: A -> Type). P a -> P b.
intros.
destruct H.
exact Hyp.
Qed.
