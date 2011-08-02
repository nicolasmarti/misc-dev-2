
Check NFoldLeft.

Require N.

Recursive sum (n: N) := if (n == 0) then 0 else n + (sum (n - 1)).

Definition sum2 (n: N) := (n * (n+1)) / 2.

Definition test (n: N) := sum n == sum2 n.

VMCompute test 10000.

