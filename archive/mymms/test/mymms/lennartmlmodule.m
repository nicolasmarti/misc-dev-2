
Inductive Person : Type :=
| isPerson: V (firstName: String) (lastName: String) (height: Float). Person.

Definition firstName p := let (isPerson x _ _) := p in x.
Definition lastName p := let (isPerson _ x _) := p in x.
Definition height p := let (isPerson _ _ x) := p in x.

Overload plus with stringConcat [0].

Require Showable.

Definition display (p: Person) : String := (firstName p) + " " + (lastName p) + ", " + (show (height p)) +  " cm ... de diametre!".

Interp display (isPerson "Nicolas" "Marti" 176).
