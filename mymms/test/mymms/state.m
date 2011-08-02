Require Monad.
Require State.
Require N.

Definition trytest : StateTrans N N := do { return 7 }.

Check trytest.

VMCompute runState trytest 6.
