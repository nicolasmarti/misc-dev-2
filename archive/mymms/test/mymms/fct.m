Require Num.
Require Float.

Inductive nexpr : Type :=
| cste: Float -> nexpr 
| var: String -> nexpr
| eadd: nexpr -> nexpr -> nexpr
| esub: nexpr -> nexpr -> nexpr
| emul: nexpr -> nexpr -> nexpr
| ediv: nexpr -> nexpr -> nexpr.

