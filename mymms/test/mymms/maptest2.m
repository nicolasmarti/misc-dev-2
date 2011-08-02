Require N.
Require Num.
Require List.
Require Map.

Recursive iota (m: N) (n: N) : list N := if n > m then conc n (iota m (n - 1)) else nil.

Definition diff (n1 n2: N) := if n1 > n2 then n1 - n2 else n2 - n1.

Recursive maxdiff (A B: Type) (m: Map A B) :=
match m with
  | Leaft ==> 0
  | Node _ _ _ l r ==> max (max (maxdiff _ _ l) (maxdiff _ _ r)) (diff (Mapsize l) (Mapsize r)).

Definition f A := \ (x: A) -> pair x x.

VMCompute maxdiff _ _ (fromlist (map (f _) (iota 0 30))).
