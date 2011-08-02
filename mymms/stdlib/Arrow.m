Open StdLib.Arrow.

Require Prod.

Open TypeClass.Definition.

Inductive Arrow A :=
  | isArrow:
	V (arr: V B C. (B -> C) -> A B C).
	V (comp: V B C D. A B C -> A C D -> A B D).
	V (first: V B C D. A B C -> A (prod B D) (prod C D)).
	    Arrow A.
Implicite isArrow [1].

Close.

Close.