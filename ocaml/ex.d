False :: Type :=

absurd :: {P :: Type} -> False -> P
absurd {P} prf := match prf with

True :: Type := | I :: True

[~) : 50 :: Type -> Type := 
| neg :: (P :: Type) -> (P -> False) -> ~ P
 
contradiction :: {P :: Type} -> P -> ~ P -> False
contradiction p (neg _ f) := f p

(/\\) : left, 40 (A B :: Type) :: Type := 
| conj :: A -> B -> A /\\ B

proj1 :: {A B :: Type} -> A /\\ B -> A
proj1 (conj a b) := a

proj2 :: {A B :: Type} -> A /\\ B -> B
proj2 (conj a b) := b

(\\/) : left, 30 (A B :: Type) :: Type :=
| left :: A -> A \\/ B
| right :: B -> A \\/ B

disj :: {A B C :: Type} -> A \\/ B -> (A -> C) -> (B -> C) -> C
disj (left a) fleft fright := fleft a
disj (right b) fleft fright := fright b

(=) : no, 20 {A:: Type} (a :: A) :: A -> Type := 
| refl :: a = a

congr :: {A :: Type} -> (P :: A -> Type) -> (a b :: A) -> a = b -> P a -> P b
congr P a b (refl) H := H
