Open StdLib.Eq.

Inductive eq A (a: A): A -> Type :=
| eqrefl: eq A a a.
Implicite eq [1].
Implicite eqrefl [1].

Lemma eq_induc2: V A (P: A -> Type) (a: A) b (H: eq a b) (H0: P b). P a.
repeat intro.
destruct H.
exact H0.
Qed.

Require Bool.

Open TypeClass.Definition.

Inductive EqDec A :=
| isEqDec:
    V (eqdec: A -> A -> bool). EqDec A.
Implicite isEqDec [1].

Close.

Definition eqdec A (H: EqDec A) :=
  match H with
    | isEqDec f ==> f.
Implicite eqdec [1].

Definition EqDecEqual A (H: EqDec A) x y :=
  eqdec H x y.
Implicite EqDecEqual [2].
Overload equal with @EqDecEqual [2].

Close.
