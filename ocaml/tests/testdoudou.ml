open Doudou

(********************************************)
(* example of source that should be process *)
(********************************************)

let example = "
Bool :: Type
True :: Bool
False :: Bool

(||) :: Bool -> Bool -> Bool
(&&) :: Bool -> Bool -> Bool

True || _ := True
_ || True := True
False || False := False

False && _ := False
_ && False := False
True && True := True

List :: Type -> Type
[[]] :: {A :: Type} -> List A
(:) :: {A :: Type} -> A -> List A -> List A

String :: Type

plusType :: Type -> Type -> Type
(+) :: {A B :: Type} -> A -> B -> plusType A B

multType :: Type -> Type -> Type
(*) :: {A B :: Type} -> A -> B -> multType A B

plusType Bool Bool := Bool
(+) {Bool} {Bool} := (||)

multType Bool Bool := Bool
(+) {Bool} {Bool} := (&&)

String :: Type

List :: Type -> Type
[[]] :: {A :: Type} -> List A
(:) :: {A :: Type} -> A -> List A -> List A

(@) :: {A :: Type} -> List A -> List A
[] @ l := l
l @ [] := l
(hd:tl) @ l := hd:(tl @ [])

map :: {A B :: Type} -> (A -> B) -> List A -> List B
map f [] := []
map f (hd:tl) := (f hd):(map f tl)

plusType (List A) (List A) := List a
(+) {List A} {List A} := (@)

multType Type Type := Type
(,) :: {A B :: Type} -> A -> B -> A * B

multType (List A) (List B) := List (List (A * B))

_ * [] := []
[] * _ := []
(hd1:tl1) * l := (map ( x := (x, hd1)) l) : (tl1 * l)

foldl :: {A B :: Type} -> (B -> A -> B) -> B -> List A -> B
foldl f acc [] := acc
foldl f acc (hd:tl) := foldl f (f acc hd) tl

foldr :: {A B :: Type} -> (A -> B -> B) -> List A -> B -> B
foldr f [] acc := acc
foldr f (hd:tl) acc := f hd (foldr f tl acc)

Nat :: Type
O :: Nat
S :: Nat -> Nat

T :: Type -> Type -> Nat -> Type
T _ B O := B
T A B (S n) := A -> T A B n

depfold :: {A B :: Type} -> (f:: B -> A -> B) -> B -> (n :: Nat) -> T A B n
depfold f acc O := acc
depfold f acc (S n) := (x := depfold f (f acc x) n)

NatPlus :: Nat -> Nat -> Nat 
NatPlus O x := x
NatPlus x O := x
NatPlus (S x) y := S (NatPlus x y)

plusType Nat Nat := Nat
(+) {Nat] {Nat} := NatPlus

depfold {Nat} (+) O (S (S 0)) :?: 
(* :?: Nat -> Nat -> Nat *)
"
(*
let _ = process_definition defs ctxt "Bool :: Type"
let _ = process_definition defs ctxt "True :: Bool"
let _ = process_definition defs ctxt "False :: Bool"
let _ = process_definition defs ctxt "(||) : left, 20 :: Bool -> Bool -> Bool"
let _ = process_definition defs ctxt "(&&) : left, 30 :: Bool -> Bool -> Bool"
let _ = process_definition defs ctxt "List :: Type -> Type"
let _ = process_definition defs ctxt "[[]] :: {A :: Type} -> List A"
let _ = process_definition defs ctxt "(:) : right, 10 :: {A :: Type} -> A -> List A -> List A"
let _ = process_definition defs ctxt "Type : ([] {Type})"
let _ = process_definition defs ctxt "Type : []"
let _ = process_definition defs ctxt "Type:Type:[]"
let _ = process_definition defs ctxt "plusType :: Type -> Type -> Type"
let _ = process_definition defs ctxt "(+) : left, 20 :: {A B :: Type} -> A -> B -> plusType A B"

let _ = process_definition defs ctxt "(+) {_} {_} True False"

let _ = process_definition defs ctxt "map :: {A B:: Type} -> (f:: A -> B) -> List A -> List B"

let _ = process_definition defs ctxt "Nat :: Type"
let _ = process_definition defs ctxt "O :: Nat"
let _ = process_definition defs ctxt "S :: Nat -> Nat"

let _ = process_definition defs ctxt "Vec :: Type -> Nat -> Type"
let _ = process_definition defs ctxt "Empty :: {A :: Type} -> Vec A O"
let _ = process_definition defs ctxt "Next :: {A :: Type} -> {n:: Nat} -> A -> Vec A n -> Vec A (S n)"

let _ = process_definition defs ctxt "prod :: Type -> Type -> Type"
let _ = process_definition defs ctxt "pair :: {A B :: Type} -> A -> B -> prod A B"

let _ = process_definition defs ctxt "\\ {A::Type} (a::A) -> a"

let _ = process_definition defs ctxt "\\ (Next {prout@(prod A B)} hd caca@Empty) -> prout"

let _ = process_definition defs ctxt "\\ (map f []) -> True"

let _ = process_definition defs ctxt "True || _ := True"
let _ = process_definition defs ctxt "_ || True := True"

let _ = process_definition defs ctxt "map"

let _ = process_definition defs ctxt "map f [] := []"
let _ = process_definition defs ctxt "map f (hd:tl) := (f hd) : map f tl"

let _ = process_definition defs ctxt "\\ (b :: Bool) -> b || False"


let _ = process_definition defs ctxt "map (\\ (b :: Bool) -> b || False) (True:False:[])"
*)

let _ = process_definition defs ctxt "List :: Type -> Type"
let _ = process_definition defs ctxt "[[]] :: {A :: Type} -> List A"
let _ = process_definition defs ctxt "(:) : right, 10 :: {A :: Type} -> A -> List A -> List A"
let _ = process_definition defs ctxt "map :: {A B:: Type} -> (f:: A -> B) -> List A -> List B"
let _ = process_definition defs ctxt "map f [] := []"
