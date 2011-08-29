open Printf;;
open Def;;

let rec print_term t =
  match t with
    | Vart v -> printf "%s" v;
    | Fctt (f, l) -> printf "%s(" f; print_list_term l; printf ")";
and print_list_term l =
  match l with
    | [] -> printf "";
    | hd :: tl -> 
        print_term hd;
        match tl with
          | [] -> printf "";
          | _ -> printf ", "; print_list_term tl;;


let rec print_formula f =
  match f with
    | Andf (f1, f2) -> printf "("; print_formula f1; printf " /\\ "; print_formula f2; printf ")";
    | Orf (f1, f2) -> printf "("; print_formula f1; printf " \\/ "; print_formula f2; printf ")";
    | Implf (f1, f2) -> printf "("; print_formula f1; printf " -> "; print_formula f2; printf ")";
    | Equiv (f1, f2) -> printf "("; print_formula f1; printf " <-> "; print_formula f2; printf ")";
    | Forallf (x, f1) -> printf "V %s. " x; printf "("; print_formula f1; printf ")";
    | Existsf (x, f1) -> printf "E %s. " x; printf "("; print_formula f1; printf ")";
    | Negf f1 -> printf "~" ; print_formula f1; 
    | Relf (r, l) -> printf "%s(" r; print_list_term l; printf ")";;


let rec print_nnf_formula f =
  match f with
    | Andnnf (f1, f2) -> printf "("; print_nnf_formula f1; printf " /\\ "; print_nnf_formula f2; printf ")";
    | Ornnf (f1, f2) -> printf "("; print_nnf_formula f1; printf " \\/ "; print_nnf_formula f2; printf ")";
    | Forallnnf (x, f1) -> printf "V %s. " x; printf "("; print_nnf_formula f1; printf ")";
    | Existsnnf (x, f1) -> printf "E %s. " x; printf "("; print_nnf_formula f1; printf ")";
    | Relnnf (b, r, l) -> (if b then (printf "~";) else (printf "";)); printf "%s(" r; print_list_term l; printf ")";;


let rec print_list_string l =
  match l with
    | [] -> printf "";
    | hd :: tl ->
        printf "%s" hd; 
        match tl with
          | [] -> printf "";
          | _ -> printf ","; print_list_string tl;;

let rec print_nnfqf_formula f =
  match f with
    | Andnnfqf (f1, f2) -> printf "("; print_nnfqf_formula f1; printf " /\\ "; print_nnfqf_formula f2; printf ")";
    | Ornnfqf (f1, f2) -> printf "("; print_nnfqf_formula f1; printf " \\/ "; print_nnfqf_formula f2; printf ")";
    | Relnnfqf (b, r, l) -> (if b then (printf "~";) else (printf "";)); printf "%s(" r; print_list_term l; printf ")";;

let rec print_cnf_lvl1' l =
  match l with
    | [] -> printf "";
    | (b, r, l) :: tl -> 
        (if b then (printf "~";) else (printf "";)); printf "%s(" r; print_list_term l; printf ")";
        match tl with
          | [] -> printf "";
          | _ ->  printf " \\/ "; print_cnf_lvl1' tl;;

let print_cnf_lvl1 l =
  match l with
    | [] -> printf "false"
    | _ -> print_cnf_lvl1' l; ;;

let rec print_cnf_lvl0' l =
  match l with
    | [] -> printf "";
    | hd :: tl -> 
        print_cnf_lvl1 hd;
        match tl with
          | [] -> printf "";
          | _ ->  printf " /\\\n"; print_cnf_lvl0' tl;;

let print_cnf_lvl0 l =
  match l with
    | [] -> printf "true"
    | _ -> print_cnf_lvl0' l; ;;

let rec print_subs s =
  match s with
    | [] -> printf "";
    | (x, t) :: tl ->
        printf "["; print_term t; printf "/ %s" x; printf "]";
        print_subs tl;;



let rec print_formula_spass f =
  match f with
    | Andf (f1, f2) -> printf "and("; print_formula_spass f1; printf ","; print_formula_spass f2; printf ")";
    | Orf (f1, f2) -> printf "or("; print_formula_spass f1; printf ", "; print_formula_spass f2; printf ")";
    | Implf (f1, f2) -> printf "implies("; print_formula_spass f1; printf ", "; print_formula_spass f2; printf ")";
    | Equiv (f1, f2) -> printf "equiv("; print_formula_spass f1; printf ", "; print_formula_spass f2; printf ")";
    | Forallf (x, f1) -> printf "forall([%s], " x; print_formula_spass f1; printf ")";
    | Existsf (x, f1) -> printf "exists([%s], " x; print_formula_spass f1; printf ")";
    | Negf f1 -> printf "not(" ; print_formula_spass f1; printf ")";
    | Relf (r, l) -> printf "%s(" r; print_list_term l; printf ")";;
