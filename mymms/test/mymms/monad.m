Require Monad.
Require Option.
Require N.
Require Num.


Definition test1 x y : option N :=
	   return (x + y).

Definition test2 x y : option N :=
	   do {
		return (x + y)
	   }.	   


Definition test3 (x y: N) : option N :=
	   do { x1 <- Some x;
	        y1 <- None;
		return (x1 + y1)
	   }.	   

Simpl test3 0 1.