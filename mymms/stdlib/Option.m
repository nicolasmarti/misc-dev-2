Open StdLib.Option.

Inductive option (A: Type) :=
| None: option A
| Some: A -> option A.
Implicite None [1].
Implicite Some [1].

Coercion @Some.

Require Monad.

Definition optionret A (a: A) :=
   Some a.

Definition optionbind A B (ma: option A) (f: A -> option B) :=
    match ma with
      | None ==> None
      | Some a ==> f a.

Definition optionfail A (s: String) : option A :=
   None.

Require Eq.

Open TypeClass.Instance.

Lemma Moption : Monad option.
  apply @isMonad.
  apply optionret.
  apply optionbind.
  apply optionfail.
Defined.

Close.

Definition fromoption A B b (f: A -> B) (o: option A) :=
   match o with
     | Some a ==> f a
     | None ==> b
.
Implicite fromoption [2].



Close.
