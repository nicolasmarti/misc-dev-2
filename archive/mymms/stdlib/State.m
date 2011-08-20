Require Monad.
Require Eq.
Require Prod.
Require Logic.

Open StdLib.State.

Inductive StateTrans (s: Type) (A: Type) :=
| stateTrans: (s -> prod A s) -> StateTrans s A.
Implicite stateTrans [2].

Definition runState (s: Type) (A: Type) (st: StateTrans s A) :=
  match st with
    | stateTrans f ==> f.
Implicite runState [2].

Definition stateReturn (s: Type) (A: Type) (a: A) : StateTrans s A :=
  stateTrans (\ s -> pair a s).

Definition stateBind (s: Type) (A B: Type) (m: StateTrans s A) (f: A -> StateTrans s B) : StateTrans s B :=
  stateTrans ( \ st -> match runState m st with
	                 | pair a s ==> let m := f a in
	                                runState m s	      

	      ).

Definition stateFail (A: Type) (s: Type) (e: String) : StateTrans s A :=
  error _ e.


Open TypeClass.Instance.

Lemma Moption : V (s: Type). Monad (StateTrans s).
  intros.
  apply @isMonad.
  intros; apply stateReturn.
  apply Hyp.
  intros; apply stateBind.
  apply A.
  apply Hyp.
  apply Hyp0.
  intros.
  apply stateFail.
  apply Hyp.
Defined.

Close.

Definition getstate (s: Type) : StateTrans s s :=
  stateTrans (\ (st: s) -> pair st st).
Implicite getstate [1].

Definition setstate (s: Type) (A: Type) (a: A) :=
  stateTrans (\ (st: s) -> pair ITrue st).
Implicite getstate [2].

Close.
