open Def;;
open Trans;;
open List;;
open Pprinter;;
open Printf;;
open Varset;;

(* application of a substitution to the CNF *)

let rec apply_subs_var x s =
  match s with
    | [] -> Vart x
    | (v, t) :: tl ->
        if (x = v) then t else apply_subs_var x tl;;

let rec apply_subs_term t s =
  match t with
    | Vart x -> apply_subs_var x s
    | Fctt (f, l) -> Fctt (f, apply_subs_listterm l s)
and apply_subs_listterm l s =
  match l with
    | [] -> []
    | hd :: tl -> (apply_subs_term hd s) :: (apply_subs_listterm tl s);;

let rec apply_subs_cnf_lvl1 l s =
  match l with
    | [] -> []
    | (b, r, l') :: tl ->
        (b, r, (apply_subs_listterm l' s)) :: (apply_subs_cnf_lvl1 tl s);;

let rec apply_subs_cnf_lvl0 l s =
  match l with
    | [] -> []
    | hd :: tl ->
        (apply_subs_cnf_lvl1 hd s) :: (apply_subs_cnf_lvl0 tl s);;

(* unification of two terms : return an option type of a list of atomic substitution *)
let rec unification_terms t1 t2 =
  match (t1, t2) with
    | (Vart x1, t2') -> (
        if (Vart x1 = t2') then
          Some ([]) else
            if (var_not_in_term x1 t2') then 
              Some ((x1, t2') :: []) else
                None
      )
    | (Fctt (f1, l1), Fctt (f2, l2)) ->
        if (f1 = f2) then
          unification_listterm l1 l2
        else
          None
    | (t2', Vart x1) -> (
        if (Vart x1 = t2') then
          Some ([]) else
            if (var_not_in_term x1 t2') then 
              Some ((x1, t2') :: []) else
                None
      )
and unification_listterm l1 l2 =
  match (l1, l2) with
    | ([], []) -> Some []
    | (hd1 :: tl1, hd2 :: tl2) -> (
        match (unification_terms hd1 hd2) with
          | None -> None
          | Some s -> (
              match (unification_listterm (apply_subs_listterm tl1 s) (apply_subs_listterm tl2 s)) with
                | None -> None
                | Some s' -> Some (s @ s')
            )
      )
    | _ -> None;;


(* composition of substitution *)
let rec apply_subst_subst_rev x t s = 
  match s with
    | [] -> []
    | (x', t') :: tl ->
        (x', apply_subs_term t' ((x,t) :: [])) :: (apply_subst_subst_rev x t tl);;

let rec comp_subs_rev s =
  match s with
    | [] -> []
    | (x, t) :: tl ->
        (x, t) :: comp_subs_rev (apply_subst_subst_rev x t tl);;

let comp_subs s = rev (comp_subs_rev (rev s));;

(* Subsumption *)

(* t1 subsum t2 (ou l'inverse ???) *)
let rec subsum_terms t1 t2 =
  match (t1, t2) with
    | (Vart x1, t2') -> (
        if (Vart x1 = t2') then
          Some ((x1,Vart x1)::[]) else
            if (var_not_in_term x1 t2') then 
              Some ((x1, t2') :: []) else
                None
      )
    | (Fctt (f1, l1), Fctt (f2, l2)) ->
        if (f1 = f2) then
          subsum_listterms l1 l2
        else
          None
    | _ -> None     
and subsum_listterms l1 l2 =
  match (l1, l2) with
    | ([], []) -> Some []
    | (hd1 :: tl1, hd2 :: tl2) -> (
        match (subsum_terms hd1 hd2) with
          | None -> None
          | Some s -> (
              match (subsum_listterms (apply_subs_listterm tl1 s) tl2) with
                | None -> None
                | Some s' -> Some (s @ s')
            )
      )
    | _ -> None;;

let subsum_listterm l1 l2 =
  match (subsum_listterms l1 l2) with
    | None -> None
    | Some s ->
        if (apply_subs_listterm l1 (comp_subs s) = l2) then
          Some s else None;;


(************************************************************************************)

(* [a partir de la, ca commence a chier ] *)


(* remove duplicate literals in clauses (without unification)
*)
let rec remove_dup_lit_clause lit c =
  match c with
    | [] -> []
    | hd :: tl -> 
        if (lit = hd) then tl else hd :: (remove_dup_lit_clause lit tl);;

let rec remove_dup_clause c =
  match c with
    | [] -> []
    | hd :: tl -> 
        hd :: (remove_dup_clause (remove_dup_lit_clause hd tl));;



(* remove tautology from clause (without unification): l a literal and c the remaining clause 
   Hyp: the literals are unique
*)
let rec remove_tauto_lit_clause lit c =
  let (b, r, l) = lit in (
      match c with
        | [] -> ([], false)
        | (b', r', l') :: tl -> 
            if ((b = not b') && (r = r') && (l = l')) then
              (tl, b) else 
                match (remove_tauto_lit_clause lit tl) with
                  | (tl', b) -> ((b', r', l') :: tl, b)

    );;

let rec remove_tauto_clause c =
    match c with
      | [] -> []
      | hd :: tl ->
          match (remove_tauto_lit_clause hd tl) with
            | (tl', true) -> remove_tauto_clause tl'
            | (_, false) -> hd :: (remove_tauto_clause tl);;

(* put it together: remove duplicate literals and tautology (without unification) *)
let remove_dup_tauto_clause c =
  remove_tauto_clause (remove_dup_clause c);;

(* apply the last function to every clause of a CNF formula *)

let rec remove_dup_tauto_CNF cnf = 
  match cnf with 
    | [] -> []
    | hd :: tl ->
        let hd' = (remove_dup_tauto_clause hd) in
          if  (remove_dup_tauto_clause hd = []) then
            (remove_dup_tauto_CNF tl) else hd' :: (remove_dup_tauto_CNF tl);;

(************************************************************************************)


let rec subsum_clause_lit l c r =
  match c with
    | [] -> []
    | hd :: tl -> (
        let tl' = (subsum_clause_lit l tl (r @ hd::[])) in 
        let (b1, r1, l1) = l in
        let (b2, r2, l2) = hd in (          

          if (b1 = b2 && r1 = r2) then (
          
            match (subsum_listterm l2 l1) with
              | None -> tl'
              | Some s -> (
                  
                  (apply_subs_cnf_lvl1 (r @ tl) (comp_subs s)) :: tl'            
                    
                )
          ) else tl'

        )
      );;

(* subsumption with back tracking (really slow) Ppoblem !!! *)

let rec subsum_clause_clause c1 c2 =  
  match c1 with
    | [] -> true
    | _ ->         
        match c2 with
          | [] -> false              
          | hd :: tl -> 
              let l = (subsum_clause_lit hd c1 []) in (

                
                (match l with
                  | [] ->
                      false
                  | _ ->
                      (subsum_clause_clause_list (l) tl)
                ) || (subsum_clause_clause c1 tl)

              )

and subsum_clause_clause_list lc c =
  match lc with
    | [] -> (false)
    | hd :: tl ->
        match hd with
          | [] -> true
          | _ ->
              if (subsum_clause_clause hd c) then true else
                (subsum_clause_clause_list tl c);;

(* if c is subsumed by some clause in f ? (strictly, or not) *)

let rec clause_cnf_subsum_strict c f =
  match f with
    | [] -> false
    | hd :: tl ->
        if (subsum_clause_clause hd c && not (subsum_clause_clause c hd)) then true else
          (clause_cnf_subsum_strict c tl)

let rec clause_cnf_subsum c f =
  match f with
    | [] -> false
    | hd :: tl ->
        if (subsum_clause_clause hd c) then 
          (true) else
          (clause_cnf_subsum c tl)

let rec simpl_cnf_subsum_strict f r =
  match f with
    | [] -> r
    | hd :: tl ->
        if (clause_cnf_subsum_strict hd (r @ tl)) then
          (simpl_cnf_subsum_strict tl r) else
          (simpl_cnf_subsum_strict tl (r @ hd::[]))

let rec simpl_cnf_subsum f r =
  match f with
    | [] -> r
    | hd :: tl ->
        if (clause_cnf_subsum hd (r @ tl)) then
          (simpl_cnf_subsum tl r) else
          (simpl_cnf_subsum tl (r @ hd::[]))

let rec listclause_cnf_subsum lc f =
  match lc with 
    | [] -> []
    | hd :: tl ->
        (if (clause_cnf_subsum hd f) then [] else hd::[]) @ (listclause_cnf_subsum tl f);;

(* equivalence trhough subsumption *)

let rec clause_in_cnf c f =
  match f with
    | [] -> false
    | hd :: tl ->
        if (subsum_clause_clause hd c && subsum_clause_clause c hd) then true else
          (clause_cnf_subsum_strict c tl)


let rec listclause_in_cnf lc f =
  match lc with 
    | [] -> []
    | hd :: tl ->
        (if (clause_in_cnf hd f) then [] else hd::[]) @ (listclause_in_cnf tl f);;


let rec simpl_in_cnf f r =
  match f with
    | [] -> r
    | hd :: tl ->
        if (clause_in_cnf hd (r @ tl)) then
          (simpl_in_cnf tl r) else
          (simpl_in_cnf tl (r @ hd::[]))

(* subsumption without back tracking (quicker) *)

let rec subsum_clause_clause2 c1 c2 =  
  match c1 with
    | [] -> true
    | _ ->         
        match c2 with
          | [] -> false              
          | hd :: tl -> 
              let l = (subsum_clause_lit hd c1 []) in (

                
                (match l with
                  | [] ->
                      false
                  | hd2::tl2 ->
                      match hd2 with
                        | [] -> true
                        | _ ->
                            (subsum_clause_clause2 hd2 tl)                      
                ) || (subsum_clause_clause2 c1 tl)

              );;

let rec clause_cnf_subsum_strict2 c f =
  match f with
    | [] -> false
    | hd :: tl ->
        if (subsum_clause_clause2 hd c && not (subsum_clause_clause2 c hd)) then true else
          (clause_cnf_subsum_strict2 c tl);;

let rec simpl_cnf_subsum_strict2 f r =
  match f with
    | [] -> r
    | hd :: tl ->
        if (clause_cnf_subsum_strict2 hd (r @ tl)) then
          (simpl_cnf_subsum_strict2 tl r) else
          (simpl_cnf_subsum_strict2 tl (r @ hd::[]));;

let rec clause_cnf_subsum2 c f =
  match f with
    | [] -> false
    | hd :: tl ->
        if (subsum_clause_clause2 hd c) then 
          (true) else
          (clause_cnf_subsum2 c tl)

let rec simpl_cnf_subsum2 f r =
  match f with
    | [] -> r
    | hd :: tl ->
        if (clause_cnf_subsum2 hd (r @ tl)) then
          (simpl_cnf_subsum2 tl r) else
          (simpl_cnf_subsum2 tl (r @ hd::[]))

let rec listclause_cnf_subsum2 lc f =
  match lc with 
    | [] -> []
    | hd :: tl ->
        (if (clause_cnf_subsum2 hd f) then [] else hd::[]) @ (listclause_cnf_subsum2 tl f);;


(* resolution *)


(*

 infer_clause3 l c [] = l' ->
  forall c' s, In (c', s) l' ->
    (c[s] <-> ~ l[s] \/ c').

*)


let rec infer_clause3 l (c: cnf_lvl1) (r: cnf_lvl1) = 
  let (b1, r1, l1) = l in
    match c with
      | [] -> []
      | (b2, r2, l2) :: tl -> (
          let tl' = (infer_clause3 l tl (r @ ((b2, r2, l2)::[]))) in (
              if ((b1 = not b2) && (r1 = r2)) then (
                match (unification_listterm l1 l2) with
                  | None -> tl'
                  | (Some s) -> (((apply_subs_cnf_lvl1 (r @ tl) (comp_subs s)), (comp_subs s))::tl')
              ) else tl'
            )
        );;


let rec dodo l c =
  match l with
    | [] -> []
    | (c', s) :: tl ->
        (c' @ (apply_subs_cnf_lvl1 c s))::(dodo tl c);;


let rec infer_clause2 c b r = 
  match c with
    | [] -> []
    | hd :: tl -> (
        let tl' = (infer_clause2 tl b (r @ hd::[])) in 
        let l = (infer_clause3 hd b []) in (
       
            ((dodo l (r @ tl)) @ tl')
          )
      )
;;

(* simpl resolution *)

let rec infer_clause1 c l = 
  match l with
    | [] -> []
    | hd :: tl -> (
        (*printf "from clause: "; print_cnf_lvl1 c; printf "\n and clause: "; print_cnf_lvl1 hd; printf "\n generate : "; print_cnf_lvl0 (infer_clause2 c hd []); printf "\n\n";*)
        (infer_clause2 c hd []) @ (infer_clause1 c tl)
      );;

(* factorisation *)

let rec factorisation (c1: cnf_lvl1) (c2: cnf_lvl1) (r1: cnf_lvl1) : cnf_lvl0 =
  match c1 with
    | [] -> []
    | hd1 :: tl1 ->
        let l = (infer_clause3 hd1 c2 []) in
          (listfactorisation l (r1 @ tl1)) @ (factorisation tl1 c2 (r1 @ hd1::[]))
and listfactorisation l c1 : cnf_lvl0 =
  match l with
    | [] -> []
    | (c2, s) :: tl -> (
        match (factorisation (apply_subs_cnf_lvl1 c1 s) c2 []) with
          | [] -> ((apply_subs_cnf_lvl1 c1 s) @ c2) :: []
          | l' -> l' ) @ (listfactorisation tl c1);;

let rec infer_factorisation c l = 
  match l with
    | [] -> []
    | hd :: tl -> (
        (*printf "from clause: "; print_cnf_lvl1 c; printf "\n and clause: "; print_cnf_lvl1 hd; printf "\n generate : "; print_cnf_lvl0 (factorisation c hd []); printf "\n\n";*)
        (factorisation c hd []) @ (infer_factorisation c tl)
      );;

let rec empty_clause_in l =
  match l with
    | [] -> false
    | ([])::tl -> true
    | hd::tl -> empty_clause_in tl;;

let rec resolution a b n  =
  (*printf "--------------------------------------------------\n";
  printf "step %d: (usable = %d, work off = %d)\n" n (List.length a) (List.length b);
  printf "--------------------------------------------------\n\n";
  printf "usable = \n"; print_cnf_lvl0 a; printf "\n\n";
  printf "work off = \n"; print_cnf_lvl0 b; printf "\n\n";*)
  match a with
    | [] -> (
        (*printf "--------------------------------------------------\n\n";
        flush stdout;*)
        printf "non";
      )
    | hd :: tl ->
        (*printf "will use: "; 
        print_cnf_lvl1 hd; printf "\n\n";
        flush stdout;*)
        let b' = (if (clause_in_cnf hd b) then b else (hd::b)) in
        let c' = (infer_clause1 hd b') in
          if (empty_clause_in c') then (printf "%d steps. " n;) else (
            let c'' = (simpl_in_cnf c' [])  in 
            let c''' =  (listclause_in_cnf c'' tl) in 
            let c'''' =  (listclause_in_cnf c''' b') in 
            let tl' = (remove_dup_tauto_CNF (listclause_in_cnf tl c'''')) in (
                
                (*printf "new rules: %d\n" (List.length c');
                print_cnf_lvl0 c'; printf "\n\n";
                
                printf "keeped rules: %d\n" (List.length c'''');
                print_cnf_lvl0 c''''; printf "\n\n";
                
                printf "--------------------------------------------------\n\n";
                flush stdout;*)
                (*resolution (tl @ c''') b' (n+1)*)
                resolution (rename_used_var_lvl0 VarSet.empty (remove_dup_tauto_CNF (tl' @ c'''')) 0) (remove_dup_tauto_CNF b') (n+1)
              )
          );;


let rec resolution2 a b n  =
  (*printf "--------------------------------------------------\n";
  printf "step %d: (usable = %d, work off = %d)\n" n (List.length a) (List.length b);
  printf "--------------------------------------------------\n\n";*)
  (*printf "usable = \n"; print_cnf_lvl0 a; printf "\n\n";*)
  (*printf "work off = \n"; print_cnf_lvl0 b; printf "\n\n";*)
  match a with
    | [] -> (
        (*printf "--------------------------------------------------\n\n";
        flush stdout;*)
        printf "non";
      )
    | hd :: tl ->
        (*printf "will use: "; 
        print_cnf_lvl1 hd; printf "\n\n";
        flush stdout;*)
        let b' = (if (clause_in_cnf hd b) then b else (hd::b)) in
        let c' = (infer_factorisation hd b') in
          if (empty_clause_in c') then (printf "%d steps. " n;) else (
            let c'' = (simpl_in_cnf c' [])  in 
            let c''' =  (listclause_in_cnf c'' tl) in 
            let c'''' =  (listclause_in_cnf c''' b') in 
            let tl' = (remove_dup_tauto_CNF (listclause_in_cnf tl c'''')) in (
                
                (*printf "new rules: %d\n" (List.length c');*)
                (*print_cnf_lvl0 c'; printf "\n\n";*)
                
                (*printf "keeped rules: %d\n" (List.length c'''');*)
                (*print_cnf_lvl0 c''''; printf "\n\n";*)
                
                (*printf "--------------------------------------------------\n\n";
                flush stdout;*)
                (*resolution (tl @ c''') b' (n+1)*)
                resolution2 (rename_used_var_lvl0 VarSet.empty (remove_dup_tauto_CNF (tl' @ c'''')) 0) (remove_dup_tauto_CNF b') (n+1)
              )
          );;


let clause_compare s1 s2 =
  (List.length s2 - List.length s1);;
