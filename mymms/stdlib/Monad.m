Require Logic.
Require Eq. 

Open StdLib.Monad.

Open TypeClass.Definition.

Inductive Monad (M: V (A: Type). Type) :=
  | isMonad:
      V (ret: V A. A -> M A).
      V (bind: V A B. M A -> (A -> M B) -> M B).
      V (fail: V A. String -> M A).
         Monad M.
Implicite isMonad [1].
Close.

Definition return M (H: Monad M) : V A. A -> M A :=
  match H with
    | isMonad r _ _ ==> r.
Implicite return [3].

Check @return.

Definition bind M (H: Monad M) : V A B. M A -> (A -> M B) -> M B :=
  match H with
    | isMonad r b _ ==> b.
Implicite bind [4].

Check @bind.

Definition fail M (H: Monad M) : V A. String -> M A :=
  match H with
    | isMonad r b f ==> f.
Implicite fail [3].

Check @bind.


Definition liftM m (H: Monad m) A B (f: A -> B) (a: m A) : m B :=
  do {
      x <- a;
      return (f x)
  }. 
Implicite lifM [4].

Check @liftM.

Close.
