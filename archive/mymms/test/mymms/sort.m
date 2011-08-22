Require Ord.
Require List.

Recursive insert A (H: Ord A) e (l: list A) [3] :=
  match l with
    | nil ==> conc e nil
    | conc hd tl ==>
       if (e < hd)
       then (conc e l)
       else (conc hd (insert A H e tl)).

Recursive insertsort A (H: Ord A) l1 l2 [2] :=
  match l1 with
    | nil ==> l2
    | conc hd tl ==>
       insertsort A H tl (insert A H hd l2).

Definition insert_sort A H l := insertsort A H l nil.
Implicite insert_sort [2].

Definition l1 := conc 32 (conc 1 (conc 12 (conc 4 nil))).

Require N.

Interp insert_sort l1.

VMCompute insert_sort l1.

Show @insert.

VMCompute (9<0).