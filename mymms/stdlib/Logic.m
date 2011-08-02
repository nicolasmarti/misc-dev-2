Open StdLib.Logic.

Inductive and A B :=
| conj: A -> B -> and A B.
Implicite conj [2].


Inductive or A B :=
| left: A -> or A B
| right: B -> or A B.
Implicite left [2].
Implicite right [2].


Inductive exists A (P: A -> Type) :=
| witness: V a. P a -> exists A P.
Implicite exists [1].
Implicite witness [2].


Inductive False : Type :=.

Inductive True : Type :=
| ITrue: True.

Definition not A := A -> False.

Close.
