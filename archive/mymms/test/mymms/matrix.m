Inductive nat : Type :=
| O : nat
| S : V (x: nat). nat.

Recursive plus (a: nat) (b: nat) [0] : nat :=
   match a with
     | b
     | \ (a: nat). S (plus a b).

Recursive mult (a: nat) (b: nat) [0] : nat :=
   match a with
     | O
     | \ (a: nat). plus b (mult a b).

Inductive vector (A: Type) : V (n0: nat). Type :=
| epsi: V (e: A). vector A O
| suiv: V (n: nat). V (e: A). V (s: vector A n). vector A (S n).

Implicite epsi [1].
Implicite suiv [1].

Definition vectorfstelt (A: Type) (n: nat) (v: vector A n) : A :=
   match v with
     | epsi e ==> e
     | suiv n e v ==> e.

Definition vectorsnd (A: Type) (n: nat) (v: vector A (S n)) : vector A n :=
   match v with
     | suiv n e v ==> v.           

Recursive buildvector (A: Type) (a: A) (n: nat) [2] : vector A n :=
   match n with
     | O ==> epsi a
     | S n ==> suiv n a (buildvector A a n).       

Recursive applyvector A B n (v1: vector (A -> B) n) (v2: vector A n) [3] : vector B n :=
   match v1 with
     | epsi f ==> (
                match v2 with
                  | epsi a ==> epsi (f a)
       )
     | suiv n f v1 ==> (
                match v2 with
                  | suiv n a v2 ==>
                            suiv n (f a) (applyvector A B n v1 v2)                  
       ).

Definition mapvector A B (f: A -> B) n (v: vector A n) :=
           applyvector A B n (buildvector (A -> B) f n) v.

Definition apply2vector A B C (f: A -> B -> C) n (va: vector A n) (vb: vector B n) : vector C n :=
       applyvector B C n (applyvector A (B -> C) n (buildvector (A -> B -> C) f n) va) vb.

Recursive foldvector A n (v: vector A n) (f: A -> A -> A) [2] : A :=
    match v with
      | epsi e ==> e
      | suiv n e v ==>
               f e (foldvector A n v f).

Definition innerproduct A 
                        (plus: A -> A -> A)
                        (mult: A -> A -> A) 
                        n (va: vector A n) (vb: vector A n) : A :=
                foldvector A n (
                     apply2vector A A A mult n va vb
                ) plus.

Definition matrix A n m :=
              vector (vector A n) m.  

Recursive buildmatrix A (a: A) n m [3] : matrix A n m :=
   match m with
     | O ==> epsi (buildvector A a n)
     | S m ==> 
             suiv m (buildvector A a n) (buildmatrix A a n m).

Recursive applymatrix A B n m (m1: matrix (A -> B) n m) (m2: matrix A n m) [4] : matrix B n m :=
   match m1 with
     | epsi c ==> (
              match m2 with
                | epsi d ==>
                          epsi (applyvector A B n c d)
       )
     | suiv m c m1 ==> (
              match m2 with
                | suiv m d m2 ==> 
                          suiv m (applyvector A B n c d) (applymatrix A B n m m1 m2)
       ). 

Definition mapmatrix A B (f: A -> B) n m (v: matrix A n m) : matrix B n m :=
           applymatrix A B n m (buildmatrix (V (a: A). B) f n m) v.

Definition apply2matrix A B C (f: A -> B -> C) n m (ma: matrix A n m) (mb: matrix B n m) : matrix C n m :=
       applymatrix B C n m (applymatrix A (B -> C) n m (buildmatrix (A -> B -> C) f n m) ma) mb.

Definition plusnatmatrix n m (ma: matrix nat n m) (mb: matrix nat n m) : matrix nat n m :=
  apply2matrix nat nat nat plus n m ma mb.

Recursive matrixfstrow A n m (mat: matrix A n m) [3] : vector A m :=
    match mat with
      | epsi e ==> epsi (vectorfstelt A n e)
      | suiv m e mat ==> 
              suiv m (vectorfstelt A n e) (matrixfstrow A n m mat).

Recursive matrixsnd A n m (mat: matrix A (S n) m) [3] : matrix A n m :=
    match mat with
      | epsi e ==> epsi (vectorsnd A n e)
      | suiv m e mat ==>
                suiv m (vectorsnd A n e) (matrixsnd A n m mat).

Recursive transpose A n m (mat: matrix A n m) [1] : matrix A m n :=
    match n with
      | O ==> epsi (matrixfstrow A n m mat)
      | S n0 ==>
           suiv n0 (matrixfstrow A n m mat) (transpose A n0 m (matrixsnd A n0 m mat)).

Recursive innervectormatrix A 
                            (plus: A-> A -> A)
                            (mult: A-> A -> A) 
                            p m  
                            (vec: vector A p) (mat: matrix A p m) [6] : vector A m :=
             match mat with
               | epsi e ==>
                         epsi (innerproduct A plus mult p vec e)
               | suiv m e mat ==>
                         suiv m (innerproduct A plus mult p vec e) 
                              (innervectormatrix
                                        A plus mult
                                        p m vec mat                              
                              ).

Recursive innermatrix A
                      (plus: A -> A -> A)
                      (mult: A -> A -> A) 
                      n p m 
                      (m1: matrix A p n) (m2: matrix A p m) [6] : matrix A m n :=
            match m1 with
              | epsi e ==>
                      epsi (innervectormatrix
                                                A plus mult
                                                p m
                                                e m2
                                        )
              | suiv n e m1 ==>
                      suiv n (innervectormatrix
                                                A plus mult
                                                p m
                                                e m2
                                          )
                                          (innermatrix
                                                A plus mult
                                                n p m
                                                m1 m2
                                          ).

Definition matrixprod A
                      (plus: A -> A -> A)
                      (mult: A -> A -> A) 
                      n p m 
                      (m1: matrix A n p) (m2: matrix A p m) : matrix A n m :=

              transpose A m n (
                   
                   innermatrix A plus mult n p m
                     (transpose A n p m1)
                     m2

              ).


Check (matrixprod).
Check (transpose).
