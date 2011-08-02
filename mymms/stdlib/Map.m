Require Ord.
Require N.
Require Prod.

Open StdLib.Map.

Inductive Map A B :=
| Leaf: Map A B
| Node: A -> B -> N -> Map A B -> Map A B -> Map A B.
Implicite Leaf [2].
Implicite Node [2].
Check Map.

Definition Mapsize A B (m: Map A B) :=
 match m with
   | Leaf ==> 0
   | Node _ _ n _ _ ==> 1 + n.
Implicite Mapsize [2].
Check @Mapsize.

Recursive Mapdepth A B (m: Map A B) [2] :=
 match m with
   | Leaf ==> 0
   | Node _ _ _ l r ==> 1 + (max (Mapdepth _ _ l) (Mapdepth _ _ l)).
Implicite Mapdepth [2].
Check @Mapdepth.

Recursive get_right_most A B (H: Ord A) n (m: Map A B)  [4] := 
   match m with
     | Leaf ==> pair Leaf (pair Leaf Leaf)
     | Node a b s l r ==>
       	    if (((Mapsize r) + 1) <= n) then (

	       pair l (pair (Node a b 0 Leaf Leaf) r)

	    ) else (

	       match get_right_most _ _ _ n r  with
	         | pair droit (pair central gauche) ==>
		   	  pair (Node a b (s + (Mapsize droit) - (Mapsize r)) l droit) 
			       (pair central gauche)

	    ).		
Implicite get_right_most [3].	
Check @get_right_most.

Recursive get_left_most A B (H: Ord A) n (m: Map A B)  [4] := 
   match m with
     | Leaf ==> pair Leaf (pair Leaf Leaf)
     | Node a b s l r ==>
           if (((Mapsize l) + 1) <= n) then (

	       pair r (pair (Node a b 0 Leaf Leaf) l)

	    ) else (

	       match get_left_most _ _ _ n l  with
	         | pair gauche (pair central droit) ==>
		   	  pair (Node a b (s + (Mapsize gauche) - (Mapsize l)) gauche r) 
			       (pair central droit)

	    ).		
Implicite get_left_most [3].	
Check @get_left_most.


Recursive set_left_most A B (H: Ord A) n (m: map A B) [4] :=
  match m with
    | Leaf ==> n
    | Node a b s l r ==>
      	   if ((s + 1) <= (Mapsize n)) then (

	      match n with
	        | Leaf ==> m
		| Node an bn sn ln _ ==>

		  Node an bn (sn + s + 1) ln m 

	   ) else (

	     let new_node := set_left_most _ _ _ n l in 
	     
	     Node a b (s + (Mapsize n)) new_node r

	   ).	   
Implicite set_left_most [3].	
Check @set_left_most.

Recursive set_right_most A B (H: Ord A) n (m: map A B) [4] :=
  match m with
    | Leaf ==> n
    | Node a b s l r ==>
      	   if ((s + 1) <= (Mapsize n)) then (

	      match n with
	        | Leaf ==> m
		| Node an bn sn _ rn ==>

		  Node an bn (sn + s + 1) m rn

	   ) else (

	     let new_node := set_right_most _ _ _ n r in 
	     
	     Node a b (s + (Mapsize n)) l new_node 

	   ).	   
Implicite set_right_most [3].	
Check @set_right_most.

Definition shift_right A B (H: Ord A) n (m: map A B) :=
   match m with
     | Leaf ==> Leaf
     | Node a b s l r ==>
         let (pair droit (pair central gauche)) := get_right_most n l in
 	 match central with
	   | Leaf ==> m
	   | Node ac bc _ _ _ ==>	     	 
	 	 Node ac bc s droit (
		      set_left_most  
		      		    (
					Node a b (Mapsize gauche) gauche Leaf
		      		    ) r

		 ).
Implicite shift_right [3].	
Check @shift_right.

Definition shift_left A B (H: Ord A) n (m: map A B) :=
   match m with
     | Leaf ==> Leaf
     | Node a b s l r ==>
         let (pair gauche (pair central droit)) := get_left_most n r in
 	 match central with
	   | Leaf ==> m
	   | Node ac bc _ _ _ ==>	     	 
	 	 Node ac bc s 
		 
		 (
		      set_right_most  
		      		    (
					Node a b (Mapsize droit) Leaf droit
		      		    ) l

		 )

		 gauche .
Implicite shift_left [3].	
Check @shift_left.

Recursive balance A B (H: Ord A) (m: map A B) delta [3] :=
   match m with
     | Leaf ==> Leaf
     | Node a b s l r ==>
         let l := (balance _ _ _ l delta) in
	 let r := (balance _ _ _ r delta) in
       	 let sl := Mapsize l in
	 let sr := Mapsize r in
         if ((sl + delta) <= sr) then
	    shift_left (sr - sl) (Node a b s l r)
	 else
	   if ((sr + delta) <= sl) then
	      shift_right (sl - sr) (Node a b s l r)
	   else Node a b s l r.
Implicite balance [3].	
Check @balance.
Show @balance.

Recursive add_node A B (H: Ord A) key val (m: map A B) [5] :=
  match m with
    | Leaf ==> pair (Node key val 0 Leaf Leaf) 1
    | Node a b s l r ==>
           match comparaison H key a with
	     | Lt ==> (
	       	  let pair nl ds := add_node _ _ _ key val l in
		    pair (Node a b (s + ds) nl r) ds		
	     )	     
	     | Eq ==> pair (Node a val s l r) 0
	     | Gt ==> (
	       	  let pair nr ds := add_node _ _ _ key val r in
		    pair (Node a b (s + ds) l nr) ds		
	     ).	     
Implicite add_node [3].	
Check @add_node.
	       	
Definition insert A B (H: Ord A) key val (m: map A B) :=      
    let pair m ds := add_node key val m in
    balance m 1.
Implicite insert [3].	
Check @insert.

Definition empty := @Leaf.
Implicite empty [2].

Require Option.

Recursive lookup A B (H: Ord A) key (m: map A B) [4] :=
    match m with
      | Leaf ==> None
      | Node a b _ l r ==>
           match comparaison H key a with
	     | Lt ==> lookup _ _ _ key l
	     | Eq ==> Some b
	     | Gt ==> lookup _ _ _ key r.
Implicite lookup [3].	
Check @lookup.
           
Recursive put_left_leaf A B n (m: map A B) [3] :=
   match m with
     | Leaf ==> n
     | Node a b s l r ==>
           let l := put_left_leaf _ _ n l in
	   Node a b (s + Mapsize n) l r.
Implicite put_left_leaf [2].	
Check @put_left_leaf.

Recursive put_right_leaf A B n (m: map A B) [3] :=
   match m with
     | Leaf ==> n
     | Node a b s l r ==>
           let r := put_right_leaf _ _ n r in
	   Node a b (s + Mapsize n) l r.
Implicite put_right_leaf [2].	
Check @put_right_leaf.

Definition join A B (H: Ord A) (m1 m2: map A B) :=
   match pair m1 m2 with
     | pair Leaf Leaf ==> Leaf
     | pair _ Leaf ==> m1
     | pair Leaf _ ==> m2
     | pair (Node _ _ s1 _ _) (Node _ _ s2 _ _) ==>
         let m := if (s1 <= s2) then
	       	     	 put_left_leaf m1 m2
	          else	 
		  	 put_left_leaf m2 m1
	 in
	 balance m 1.
Implicite joint [3].	
Check @join.

Recursive remove A B (H: Ord A) key (m: map A B) [4] :=
    match m with
      | Leaf ==> m
      | Node a b s l r ==>
           match comparaison H key a with
	     | Lt ==> 
	       	      let l := remove _ _ _ key l in
		      Node a b s l r
	     | Eq ==> join _ _ _ l r
	     | Gt ==> 
	       	      let r := remove _ _ _ key r in
		      Node a b s l r.
Implicite remove [3].	
Check @remove.

Recursive fold A B C (f: A -> B -> C -> C) c (m: Map A B) [5] :=
  match m with
    | Leaf ==> c
    | Node a b _ l r ==> 
      	   let c1 := fold _ _ _ f c l in
	   let c2 := f a b c1 in
	       fold _ _ _ f c2 l.
Implicite fold [3].	
Check @fold.

Recursive map A B C (f:  B -> C) (m: Map A B) [4] :=
  match m with
    | Leaf ==> Leaf
    | Node a b s l r ==> Node a (f b) s (map _ _ _ f l) (map _ _ _ f r).
Implicite map [3].	
Check @map.

Require List.
Require Prod.

Definition tolist A B (m: Map A B) :=
  Map.fold (\ key val acc. conc (pair key val) acc) nil m.
Implicite tolist [2].	
Check @tolist.

Definition fromlist A B (H: Ord A) (l: list (prod A B)) :=
  List.foldl 
    (\ acc hd .
       	  let pair key val := hd in
	  insert key val acc
	  )
    Leaf
    l.
Implicite fromlist [3].
Check @fromlist.

Close.
