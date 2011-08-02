Open Editor.Base.

Require List.
Require N.
Require Z.
Require Prod.


Inductive Input :=
| add: Char -> Input
| resize: N -> N -> Input
| moverel: Z -> Z -> Input
| moveabs: N -> N -> Input.

Inductive Output :=
| print: N -> N -> Char -> Output
| movecursor: N -> N -> Output.

Open TypeClass.Definition.

Inductive Buffer A :=
| isBuffer:
    V (empty: A). 
    V (onInput: list Input -> A).
    V (offOutput: A -> list Output).
    V (rstOutput: A -> A).
    Buffer A.
Implicite isBuffer [1].

Close.

Definition emptyBuffer A (H: Buffer A) :=
   match H with
     | isBuffer e _ _ _ ==> e.
Implicite emptyBuffer [2].

Definition onInput A (H: Buffer A) :=
   match H with
     | isBuffer _ i _ _ ==> i.
Implicite onInput [2].

Definition offOutput A (H: Buffer A) :=
   match H with
     | isBuffer _ _ o _ ==> o.
Implicite offOutput [2].

Definition rstOutput A (H: Buffer A) :=
   match H with
     | isBuffer _ _ _ r ==> r.
Implicite rstOutput [2].

Definition zipper A := prod (list A) (list A).

Recursive shift_rel_right A (l1: list A) (l2: list A) (n: N) [1] :=
   match l1 with
     | nil ==> pair l1 l2
     | conc hd1 tl1 ==> if (n == 0) then pair l1 l2 else
       	    	    	shift_rel_right A tl1 (conc hd1 l2) (n - 1).
Implicite shift_rel_right [1].

Recursive shift_rel_left A (l1: list A) (l2: list A) (n: N) [2] :=
   match l2 with
     | nil ==> pair l1 l2
     | conc hd2 tl2 ==> if (n == 0) then pair l1 l2 else
       	    	    	shift_rel_left A (conc hd2 l1) tl2  (n - 1).
Implicite shift_rel_left [1].

Definition shift_rel A (l: zipper A) (n: Z) :=
   let pair l1 l2 := l in
   if (n >= 0) then 
      shift_rel_right l1 l2 (ZAbs n)
   else
      shift_rel_left l1 l2 (ZAbs n).
Implicite shift_rel [1].   

Definition shift_abs A (l: zipper A) (n: N) :=
   let pair l1 l2 := l in 
   let n_rel := NMinusZ (length l1) n in
   shift_rel l n_rel.
Implicite shift_abs [1].   

Inductive buffer_state :=
| buffer_st:
   V (buf: zipper (zipper Char)).
   buffer_state.

Definition init_buffer_state :=
  buffer_st (pair nil nil).


Close.
