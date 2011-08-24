Inductive nat : Type :=
| O: nat
| S: nat -> nat.

Inductive eq A (a: A) : A -> Type :=
| eqrefl: eq A a a.

Lemma congruence_nat: V (x y: nat). eq nat (S x) (S y) -> eq nat x y.
intros.
destruct Hyp.
apply eqrefl.
Qed.
