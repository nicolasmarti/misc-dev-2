Open StdLib.Prod.

Inductive prod A B :=
| pair: A -> B -> prod A B.
Implicite pair [2].

Close.
