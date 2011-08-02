Require Ord.

Inductive Tree (A: Type) (OrdA: Ord A) : Type :=
| Null: Tree A OrdA
| Fork: A -> (Tree A OrdA) -> (Tree A OrdA) -> (Tree A OrdA).
Implicite Null [2].
Implicite Fork [2].

Definition isEmpty (A: Type) (OrdA: Ord A) (t: Tree A OrdA) : Bool :=
  match t with
    | Null ==> true
    | _ ==> false.
Implicite isEmpty [2].
Check @isEmpty.

Definition minElem (A: Type) (OrdA: Ord A) (t: Tree A OrdA) : A :=
  match t with
    | Fork x _ _ ==> x
    | _ ==> error "a".
Implicite minElem [2].
Check @minElem.

Recursive join A (OrdA: Ord A) (t1 t2: Tree A OrdA) : Tree A OrdA :=
match t1 with
  | Fork x a b ==> Fork x b (merge _ _ a t2)
  | _ ==> error "a"
with merge A (OrdA: Ord A) (t1 t2: Tree A OrdA) : Tree A OrdA :=
match pair t1 t2 with
  | pair a Null ==> a
  | pair Null b ==> b
  | pair a b ==> if minElem a > minElem b then join _ _ a b else join _ _ b a
.
Implicite join [2].
Implicite merge [2].
Check @join.
Check @merge.

Definition insert A (OrdA: Ord A) x (a: Tree A OrdA) :=
  join (Fork x Null Null) a.
Implicite insert [2].
Check @insert.

Require List.

Definition fromList (A: Type) (OrdA: Ord A) (l: list A) : Tree A OrdA :=
  foldl (\ acc hd -> insert hd acc) Null l.
Implicite fromList [2].

Require N.

Recursive iota (m: N) (n: N) : list N := if n >= m then conc m (iota (m+1) n) else nil.

Interp fromList (iota 1 10).

Interp insert 2 (insert 1 Null).

