Open StdLib.List.

Inductive list A :=
| nil: list A
| conc: A -> list A -> list A.
Implicite nil [1].
Implicite conc [1].

Definition lift2list A (a: A) := conc a nil.
Coercion lift2list.

Require N.

Recursive length A (l: list A) [1] :=
  match l with
    | nil ==> 0
    | conc hd tl ==> 1 + (length _ tl).
Implicite length [1].

Recursive app A (l1 l2: list A) [1] :=
  match l1 with
    | nil ==> l2
    | conc hd tl ==> conc hd (app _ tl l2).
Implicite app [1].

Recursive revapp A (l1 l2: list A) [1] :=
  match l1 with
    | nil ==> l2
    | conc hd tl ==> revapp _ tl (conc hd l2).
Implicite revapp [1].

Definition rev A (l: list A) :=
  revapp l nil.
Implicite rev [1].

Recursive map A B (f: A -> B) (l: list A) [3] :=
   match l with
     | nil ==> nil
     | conc hd tl ==> conc (f hd) (map _ _ f tl).
Implicite map [2].

Recursive foldl A B (f: A -> B -> A) a l [4] :=
   match l with
     | nil ==> a
     | conc hd tl ==>
       	     foldl _ _ f (f a hd) tl .
Implicite foldl [2].

Recursive foldr A B (f: B -> A -> A) a l [4] :=
   match l with
     | nil ==> a
     | conc hd tl ==>
       	     f hd (foldr _ _ f a tl).
Implicite foldr [2].

Recursive intercalate A a (l: list A) [2] :=
  match l with
    | conc hd1 (conc hd2 tl) ==> conc hd1 (conc a (intercalate _ a (conc hd2 tl)))
    | _ ==> l.
Implicite intercalate [1].

Require Option.

Definition head A (l: list A) :=
  match l with
    | nil ==> None
    | conc hd tl ==> Some hd.
Implicite head [1].

Definition tail A (l: list A) :=
  match l with
    | nil ==> None
    | conc hd tl ==> Some tl.
Implicite tail [1].

Recursive init A (l: list A) [1] :=
  match l with
    | nil ==> None
    | conc hd nil ==> Some nil
    | conc hd tl ==> 
       match (init _ tl) with
         | None ==> None
	 | Some tl2 ==> Some (conc hd tl2).              
Implicite init [1].

Require Prod.

Recursive zipwith A B C (f: A -> B -> C) l1 l2 [4] :=
  match pair l1 l2 with
    | pair (conc hd1 tl1) (conc hd2 tl2) ==> (
	    conc (f hd1 hd2) (zipwith _ _ _ f tl1 tl2)
    )
    | _ ==> nil.
Implicite zipwith [3].

Recursive compare_list A (H: Ord A) (l1 l2: list A) [2] :=
   match (pair l1 l2) with
     | pair nil nil ==> Eq
     | pair (conc hd1 tl1) (conc hd2 tl2) ==> 
        (
           match (comparaison _ hd1 hd2) with
	     | Eq ==> compare_list _ H tl1 tl2
	     | cp ==> cp
        )
     | pair nil _ ==> Lt
     | pair _ nil ==> Gt.
Implicite compare_list [2].

Recursive filter A (l: list A) (P: A -> bool) [1] :=
   match l with
     | nil ==> nil
     | conc hd tl ==> 
         if (P hd) then (conc hd (filter A tl P)) else (filter A tl P).
			

Close.

Open TypeClass.Instance.

Definition ListOrd A (H: Ord A) :=
  isOrd (@compare_list A H).

Close.
