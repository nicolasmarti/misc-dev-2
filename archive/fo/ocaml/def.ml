
type var = string;;

type fct = string;;

type rel = string;;


type term =
  | Vart of var
  | Fctt of fct * term list;;

type formula =
  | Andf of formula * formula
  | Orf of formula * formula
  | Implf of formula * formula
  | Equiv of formula * formula
  | Forallf of var * formula
  | Existsf of var * formula
  | Negf of formula
  | Relf of rel * term list;;

type nnf_formula =
  | Andnnf of nnf_formula * nnf_formula
  | Ornnf of nnf_formula * nnf_formula
  | Forallnnf of var * nnf_formula
  | Existsnnf of var * nnf_formula
  | Relnnf of bool * rel * term list;;

type nnf_qf_formula =
  | Andnnfqf of nnf_qf_formula * nnf_qf_formula
  | Ornnfqf of nnf_qf_formula * nnf_qf_formula
  | Relnnfqf of bool * rel * term list;;

type nnf_pf_formula =
  | Forallnnfpf of var * nnf_pf_formula
  | Existsnnfpf of var * nnf_pf_formula
  | Nnf_qf_formula of nnf_qf_formula;;

type cnf_lvl1 = (bool * rel * term list) list;;

type cnf_lvl0 = cnf_lvl1 list;;


