open Def;;
open String;;
open Printf;;
open Pprinter;;
open Varset;;

(* replace a variable by a term inside a term *)
let rec rewrite_var_term t from into =
  match t with
    | Vart x -> if (from = x) then into else t
    | Fctt (f, l) -> Fctt (f, rewrite_var_listterm l from into)
and rewrite_var_listterm l from into =
  match l with
    | [] -> []
    | hd :: tl -> (rewrite_var_term hd from into) :: (rewrite_var_listterm tl from into);;

(* rename a variable inside a formula *)
let rec rename_formula_var f from into =
  match f with
    | Existsf (x, f1) -> 
        if (x = from) then (Existsf (into, rename_formula_var f1 from into)) else
          (Existsf (x, rename_formula_var f1 from into))
    | Forallf (x, f1) -> 
        if (x = from) then (Forallf (into, rename_formula_var f1 from into)) else
          (Forallf (x, rename_formula_var f1 from into))
    | Orf (f1, f2) -> 
        Orf ((rename_formula_var f1 from into), (rename_formula_var f2 from into))
    | Andf (f1, f2) -> 
        Andf ((rename_formula_var f1 from into), (rename_formula_var f2 from into))
    | Implf (f1, f2) -> 
        Implf ((rename_formula_var f1 from into), (rename_formula_var f2 from into))
    | Equiv (f1, f2) -> 
        Equiv ((rename_formula_var f1 from into), (rename_formula_var f2 from into))
    | Negf f1 -> 
        Negf (rename_formula_var f1 from into)
    | Relf (r, l) -> 
        Relf (r,  (rewrite_var_listterm l from (Vart into)));;

(* rename a variable inside a nnf formula *)
let rec rename_nnfformula_var f from into =
  match f with
    | Existsnnf (x, f1) -> 
        if (x = from) then (Existsnnf (into, rename_nnfformula_var f1 from into)) else
          (Existsnnf (x, rename_nnfformula_var f1 from into))
    | Forallnnf (x, f1) -> 
        if (x = from) then (Forallnnf (into, rename_nnfformula_var f1 from into)) else
          (Forallnnf (x, rename_nnfformula_var f1 from into))
    | Ornnf (f1, f2) -> 
        Ornnf ((rename_nnfformula_var f1 from into), (rename_nnfformula_var f2 from into))
    | Andnnf (f1, f2) -> 
        Andnnf ((rename_nnfformula_var f1 from into), (rename_nnfformula_var f2 from into))
    | Relnnf (b, r, l) -> 
        Relnnf (b, r,  (rewrite_var_listterm l from (Vart into)));;

(* replace a variable by a term inside a qf nnf formula *)
let rec rewrite_var_qfnnfformula f from into =
  match f with
    | Ornnfqf (f1, f2) -> 
        Ornnfqf ((rewrite_var_qfnnfformula f1 from into), (rewrite_var_qfnnfformula f2 from into))
    | Andnnfqf (f1, f2) -> 
        Andnnfqf ((rewrite_var_qfnnfformula f1 from into), (rewrite_var_qfnnfformula f2 from into))
    | Relnnfqf (b, r, l) -> 
        Relnnfqf (b, r,  (rewrite_var_listterm l from into));;

(* return a fresh name in a list of name
   methods: list traversal where (try to appends the number 0 if a name matches)
*)


let rec add_string_index (y: string) index =
  let len = (length y - index) in
  match (String.get y len) with
    | '0' -> (set y len '1'); y
    | '1' -> (set y len '2'); y
    | '2' -> (set y len '3'); y
    | '3' -> (set y len '4'); y
    | '4' -> (set y len '5'); y
    | '5' -> (set y len '6'); y
    | '6' -> (set y len '7'); y
    | '7' -> (set y len '8'); y
    | '8' -> (set y len '9'); y
    | '9' -> (set y len '0'); (add_string_index (y: string) (index + 1));
    | c -> (concat "" (y :: "0" :: [])) ;;


let add_index_string y = add_string_index y 1;;

let rec fresh_name_list_name' l x =
  (*printf "%s fresh in {" x ; print_list_string l; printf "}? %b\n" (is_fresh_name l x);*)
  if (not (VarSet.subset (VarSet.singleton x) l)) then x else (
    (fresh_name_list_name' l (add_index_string x))
  );;

let fresh_name_list_name l x = fresh_name_list_name' l (copy x);;


(* rewrite the formula such that all variables have different names *)

let rec formula2cf' f l =
  match f with
    | Existsf (x, f1) -> 
        if (VarSet.subset (VarSet.singleton x) l) then
          let z = x in
          let y = (fresh_name_list_name l z) in 
          let (f1', l') = (formula2cf' f1 (y ++ l)) in
            (Existsf (y, rename_formula_var f1' x y), (y ++ l))
        else
          let (f1', l') = (formula2cf' f1 (x ++ l)) in
            (Existsf (x, f1'), l');
    | Forallf (x, f1) -> 
        if (VarSet.subset (VarSet.singleton x) l) then
          let z = x in
          let y = (fresh_name_list_name l z) in 
          let (f1', l') = (formula2cf' f1 (y ++ l)) in
            (Forallf (y, rename_formula_var f1' x y), (y ++ l))                
        else
          let (f1', l') = (formula2cf' f1 (x ++ l)) in 
            (Forallf (x, f1'), l')                                   
    | Orf (f1, f2) ->
        let (f1', l1) = (formula2cf' f1 l) in
        let (f2', l2) = (formula2cf' f2 l1) in
          (Orf (f1', f2'), l2)
    | Andf (f1, f2) -> 
        let (f1', l1) = (formula2cf' f1 l) in
        let (f2', l2) = (formula2cf' f2 l1) in
          (Andf (f1', f2'), l2)
    | Implf (f1, f2) -> 
        let (f1', l1) = (formula2cf' f1 l) in
        let (f2', l2) = (formula2cf' f2 l1) in
          (Implf (f1', f2'), l2)
    | Equiv (f1, f2) -> 
        let (f1', l1) = (formula2cf' f1 l) in
        let (f2', l2) = (formula2cf' f2 l1) in
          (Equiv (f1', f2'), l2)
    | Negf f1 -> 
        let (f1', l1) = (formula2cf' f1 l) in  
          (Negf f1', l1)
    | Relf (r, l') -> (Relf (r, l'), l);;


let formula2cf f = 
  (*printf "formula2cf (\n";
  print_formula f;
dn  printf ")\n";*)
  let (f', l') = (formula2cf' f VarSet.empty) in f';;

(* rewrite the nnfformula such that all variables have different names *)

let rec nnfformula2cf' f l =
  match f with
    | Existsnnf (x, f1) -> 
        if (VarSet.subset (VarSet.singleton x) l) then
          let z = x in
          let y = (fresh_name_list_name l z) in 
          let (f1', l') = (nnfformula2cf' f1 (y ++ l)) in
            (Existsnnf (y, rename_nnfformula_var f1' x y), (y ++ l))
        else
          let (f1', l') = (nnfformula2cf' f1 (x ++ l)) in
            (Existsnnf (x, f1'), l');
    | Forallnnf (x, f1) -> 
        if (VarSet.subset (VarSet.singleton x) l) then
          let z = x in 
          let y = (fresh_name_list_name l z) in 
          let (f1', l') = (nnfformula2cf' f1 (y ++ l)) in
            (Forallnnf (y, rename_nnfformula_var f1' x y), (y ++ l))                
        else
          let (f1', l') = (nnfformula2cf' f1 (x ++ l)) in 
            (Forallnnf (x, f1'), l')                                   
    | Ornnf (f1, f2) ->
        let (f1', l1) = (nnfformula2cf' f1 l) in
        let (f2', l2) = (nnfformula2cf' f2 l1) in
          (Ornnf (f1', f2'), l2)
    | Andnnf (f1, f2) -> 
        let (f1', l1) = (nnfformula2cf' f1 l) in
        let (f2', l2) = (nnfformula2cf' f2 l1) in
          (Andnnf (f1', f2'), l2)
    | Relnnf (b, r, l') -> (Relnnf (b, r, l'), l);;


let nnfformula2cf f = 
  (* printf "nnfformula2cf\n";
  print_nnf_formula f;
  printf ")\n";*)
  let (f', l') = (nnfformula2cf' f VarSet.empty) in f';;


(* transform a formula into its NNF *)

let rec formula2nnf b f =
  match f with
    | Existsf (x, f1) -> if b then (Forallnnf (x, (formula2nnf true f1))) else (Existsnnf (x, (formula2nnf false f1)))
    | Forallf (x, f1) -> if b then (Existsnnf (x, (formula2nnf true f1))) else (Forallnnf (x, (formula2nnf false f1)))
    | Orf (f1, f2) -> if b then (Andnnf ((formula2nnf true f1), (formula2nnf true f2))) else (Ornnf ((formula2nnf false f1), (formula2nnf false f2)))
    | Andf (f1, f2) -> if b then (Ornnf ((formula2nnf true f1), (formula2nnf true f2))) else (Andnnf ((formula2nnf false f1), (formula2nnf false f2)))
    | Implf (f1, f2) -> if b then
        Andnnf ((formula2nnf false f1),(formula2nnf true f2)) else
          Ornnf ((formula2nnf true f1), (formula2nnf false f2))
    | Equiv (f1, f2) -> 
        formula2nnf b (Andf(Implf(f1,f2),Implf(f2,f1)))
    | Negf f1 -> (formula2nnf (not b) f1)
    | Relf (r, l) -> Relnnf (b, r, l);;

(* push quantification *)

(* a variable is not inside a term *)
let rec var_not_in_term x t =
  match t with
    | Vart y -> not (x = y)
    | Fctt (f, l) -> var_not_in_listterm x l
and var_not_in_listterm x l =
  match l with
    | [] -> true
    | hd :: tl ->
        if (var_not_in_term x hd) then 
          var_not_in_listterm x tl else
            false;;

(* a variable is not inside a formula *)
let rec var_not_in_formula v f =
  match f with
    | Existsf (x, f1) -> if (x = v) then true else (var_not_in_formula v f1)
    | Forallf (x, f1) -> if (x = v) then true else (var_not_in_formula v f1)
    | Orf (f1, f2) -> (var_not_in_formula v f1) && (var_not_in_formula v f2)
    | Andf (f1, f2) -> (var_not_in_formula v f1) && (var_not_in_formula v f2) 
    | Implf (f1, f2) -> (var_not_in_formula v f1) && (var_not_in_formula v f2)
    | Equiv (f1, f2) -> (var_not_in_formula v f1) && (var_not_in_formula v f2)
    | Negf f1 -> (var_not_in_formula v f1)
    | Relf (r, l) -> var_not_in_listterm v l;;

(* a variable is not inside a nnf formula *)
let rec var_not_in_nnfformula v f =
  match f with
    | Existsnnf (x, f1) -> if (x = v) then true else (var_not_in_nnfformula v f1)
    | Forallnnf (x, f1) -> if (x = v) then true else (var_not_in_nnfformula v f1)
    | Ornnf (f1, f2) -> (var_not_in_nnfformula v f1) && (var_not_in_nnfformula v f2)
    | Andnnf (f1, f2) -> (var_not_in_nnfformula v f1) && (var_not_in_nnfformula v f2) 
    | Relnnf (b, r, l) -> var_not_in_listterm v l;;

(* push quantifiers in nnf formula *)

let rec push_quant_nnfformula f =
  match f with
    | Existsnnf (x, f1) -> 
        let f1' = (push_quant_nnfformula f1) in (
        if (var_not_in_nnfformula x f1') then
          f1' else
            match f1' with
              | Ornnf (f11, f12) -> 
                  Ornnf (push_quant_nnfformula (Existsnnf (x, f11)), push_quant_nnfformula (Existsnnf (x, f12)))
              | Andnnf (f11, f12) ->
                  if (var_not_in_nnfformula x f11) then
                    Andnnf (push_quant_nnfformula f11, push_quant_nnfformula (Existsnnf (x, f12))) else
                      if (var_not_in_nnfformula x f12) then
                        Andnnf (push_quant_nnfformula (Existsnnf (x, f11)), push_quant_nnfformula f12) else
                          Existsnnf (x, push_quant_nnfformula f1')
              | _ -> Existsnnf (x, push_quant_nnfformula f1')
      )
    | Forallnnf (x, f1) -> 
        let f1' = (push_quant_nnfformula f1) in (
        if (var_not_in_nnfformula x f1') then
          f1' else
            match f1' with
              | Andnnf (f11, f12) -> 
                  Andnnf (push_quant_nnfformula (Forallnnf (x, f11)), push_quant_nnfformula (Forallnnf (x, f12)))
              | Ornnf (f11, f12) ->
                  if (var_not_in_nnfformula x f11) then
                    Ornnf (push_quant_nnfformula f11, push_quant_nnfformula (Forallnnf (x, f12))) else
                      if (var_not_in_nnfformula x f12) then
                        Ornnf (push_quant_nnfformula (Forallnnf (x, f11)), push_quant_nnfformula f12) else
                          Forallnnf (x, push_quant_nnfformula f1')
              | Forallnnf (y, f1'') ->
                Forallnnf (y, push_quant_nnfformula (Forallnnf (x,f1'')))
              | _ -> Forallnnf (x, push_quant_nnfformula f1')
      )
    | Ornnf (f1, f2) -> Ornnf (push_quant_nnfformula f1, push_quant_nnfformula f2)
    | Andnnf (f1, f2) -> Andnnf (push_quant_nnfformula f1, push_quant_nnfformula f2) 
    | Relnnf (b, r, l) -> f ;;


(* remove quantifier *)

let rec term_fv l t =
  match t with
    | Vart x -> if (VarSet.subset (VarSet.singleton x) l) then (VarSet.singleton x) else VarSet.empty
    | Fctt (f, l') -> listterm_fv l l'
and listterm_fv l l' =
  match l' with
    | [] -> VarSet.empty
    | hd :: tl -> (term_fv l hd) +++ (listterm_fv l tl);;


let rec formulannf_fv l f =
  match f with
    | Andnnf (f1, f2) -> 
        (formulannf_fv l f1) +++ (formulannf_fv l f2)
    | Ornnf (f1, f2) -> 
        (formulannf_fv l f1) +++ (formulannf_fv l f2)
    | Forallnnf (x, f1) -> 
        (formulannf_fv (x ++ l) f1)
    | Existsnnf (x, f1) ->       
        (formulannf_fv (x ++ l) f1)           
    | Relnnf (b, r, l') -> 
        listterm_fv l l';;
          
let rec list_var2list_term l =
  match l with
    | [] -> []
    | hd :: tl ->
        (Vart hd) :: (list_var2list_term tl);;

let rec formulannf2qf f l =
  match f with
    | Andnnf (f1, f2) -> Andnnfqf ((formulannf2qf f1 l), (formulannf2qf f2 l))
    | Ornnf (f1, f2) -> Ornnfqf ((formulannf2qf f1 l), (formulannf2qf f2 l))
    | Forallnnf (x, f1) -> (formulannf2qf f1 (x ++ l))
    | Existsnnf (x, f1) ->
        (rewrite_var_qfnnfformula (formulannf2qf f1 l) x 
           (Fctt (concat "" ("f" :: x :: []), 
                  (list_var2list_term (VarSet.elements (VarSet.inter (formulannf_fv l f1) l)))
                 )
           )
        )
          
    | Relnnf (b, r, l') -> Relnnfqf (b, r, l');;

(* CNF *)

let rec cnf_lvl1_or_cnf_lvl0 (l1: cnf_lvl1) (l0: cnf_lvl0) =
  match l0 with
    | [] -> []
    | hd :: tl -> ((l1 @ hd) :: []) @ (cnf_lvl1_or_cnf_lvl0 l1 tl);;

let rec cnf_lvl0_or_cnf_lvl0 l l' =
  match l with
    | [] -> []
    | hd :: tl -> (cnf_lvl1_or_cnf_lvl0 hd l') @ (cnf_lvl0_or_cnf_lvl0 tl l');;

let rec formulannfqf2cnf f =
  match f with
    | Andnnfqf (f1, f2) -> (formulannfqf2cnf f1) @ (formulannfqf2cnf f2)
    | Ornnfqf (f1, f2) -> cnf_lvl0_or_cnf_lvl0 (formulannfqf2cnf f1) (formulannfqf2cnf f2)
    | Relnnfqf (b, r, l) -> (((b,r,l) :: []) :: []);;

(* cf of cnf *)

(* a reimplementer avec des sets ... *)

let rec term_listvar t =
  match t with
    | Vart x -> (VarSet.singleton x)
    | Fctt (f, l) -> listterm_listvar l
and listterm_listvar l =
  match l with
    | [] -> VarSet.empty
    | hd :: tl -> (term_listvar hd) +++ (listterm_listvar tl);;

let rec lvl1_listvar l =
  match l with
    | [] -> VarSet.empty
    | (b, r, l')::tl ->
        ((listterm_listvar l') +++ (lvl1_listvar tl)) ;;

let rec rewrite_var_lvl1 l from into =
  match l with
    | [] -> []
    | (b, r, l') :: tl ->
        (b,r, (rewrite_var_listterm l' from into)) :: (rewrite_var_lvl1 tl from into);;

let rec lvl0_listvar l =
  match l with
    | [] -> VarSet.empty
    | hd::tl ->
        ((lvl1_listvar hd) +++ (lvl0_listvar tl)) ;;


(* canonical form for CNF *)
let rec rename_usedvar_lvl1  lrv luv c =
  match lrv with 
    | [] -> c
    | hd :: tl -> 
        let hd' = (fresh_name_list_name luv hd) in (
            (*printf "!"; flush stdout;*)
            (rename_usedvar_lvl1 tl luv
               (rewrite_var_lvl1 c hd (Vart hd'))
            )
          );;
  

let rec rename_used_var_lvl0 luv l n =
  match l with
    | [] -> []
    | hd :: tl ->
        let hd' = (rename_usedvar_lvl1 (VarSet.elements (VarSet.inter luv (lvl1_listvar hd))) luv hd) in (
            (*printf ": %d \t\t" n; flush stdout;*)
            ((hd')::(rename_used_var_lvl0 (luv +++ (lvl1_listvar hd')) tl (n+1)))
          );;
