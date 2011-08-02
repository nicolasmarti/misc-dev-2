Require Bool.

Inductive term : Type -> Type :=
| Encap: V (A: Type). A -> term A
| App: V (A: Type). V (B: Type). term (A -> B) -> term A -> term B
| Ifte: V (A: Type). term bool -> term A -> term A -> term A.

Implicite Encap [1].
Implicite App [2].
Implicite Ifte [1].


Recursive execterm A (t: term A) [1] : _ :=
   match t with
     | Encap x ==> x
     | App tab ta ==> (execterm _ tab) (execterm _ ta)
     | Ifte tb t1 t2 ==> 
                match (execterm _ tb) with
                  | execterm _ t1
                  | execterm _ t2
.

Implicite execterm [1].


Inductive nat : Type :=
| O: nat
| S: nat -> nat.

Require Prod.

Recursive eqnat (x:nat) (y:nat) [0] :=
  match (pair x y) with
    | pair O O ==> true
    | pair (S x) (X y) ==> eqnat x y
    | _ ==> false.


Check (Encap O).

Check (App (Encap eqnat) (Encap O)).

Check (App (App (Encap eqnat) (Encap O)) (Encap O)).

Definition t := (Ifte (App (App (Encap eqnat) (Encap O)) (Encap O)) (Encap O) (Encap (S O))).

Check t.

Simpl t.

Simpl (execterm t).
