
%{
  open Printf;;
  open Lexing;;
  open Def;;
  open Trans;;
  open Pprinter;;
  open Solve;;
  open Varset;;


  let rec listname2Forallf ln f =
    match ln with
      | [] -> f
      | hd :: tl ->
          Forallf (hd, listname2Forallf tl f);;

  let rec listname2Existsf ln f =
    match ln with
      | [] -> f
      | hd :: tl ->
          Existsf (hd, listname2Existsf tl f);;

  let resolve_formula f =
    printf "***********************************\n";
    printf "formula f:\n"; print_formula f; printf "\n"; 
    (*printf "SPASS :\n"; print_formula_spass f; printf "\n\n";*)
    printf "-----------------------------------\n";
    let f1 = (formula2cf (Negf f)) in
    let f2 = (formula2nnf false f1) in 
    let f3 = (push_quant_nnfformula f2) in
    let f4 = (nnfformula2cf f3) in
    let f5 = (formulannf2qf f4 VarSet.empty) in
    let f6 = (formulannfqf2cnf f5) in
    let f7 = (remove_dup_tauto_CNF f6) in
      (*printf "subsum !\n" ; flush stdout;*)
      let f8 = (simpl_cnf_subsum f7 []) in 
        (*printf "nb_clause: %d\n" (List.length f8); flush stdout;*)
        let f9 = (rename_used_var_lvl0 VarSet.empty f8 0) in
        let f10 = (simpl_cnf_subsum f9 []) in 	
	(*
          printf "\n-----------------------------------\n";
          printf "negation: "; print_formula f1; printf "\n\n";
          printf "NNF: "; print_nnf_formula f2; printf "\n\n";
          printf "PQ: "; print_nnf_formula f3; printf "\n\n";
          printf "CF: "; print_nnf_formula f4; printf "\n\n";
          printf "QF: "; print_nnfqf_formula f5; printf "\n\n";
          printf "CNF: "; print_cnf_lvl0 f7; printf "\n\n";
	  *)
          (*printf "Final: "; print_cnf_lvl0 (List.sort clause_compare f10); printf "\n\n";*)
          printf "nb clauses: %d\n" (List.length f10);        
          printf "resolution2 found empty clause ?: "; flush stdout;
          (resolution2 (List.sort clause_compare f10) [] 1); printf "\n"; flush stdout;
	  (*
          printf "resolution found empty clause ?: "; flush stdout;
          (resolution (List.sort clause_compare f10) [] 1); printf "\n"; flush stdout;
	  *)
          printf "-----------------------------------\n\n";;

%}

/*  */
%token NEWLINE EOF

/* The indentifiers for functions and relations */
%token <string> NAME

  /* The connectives */
%token AND AND2 OR BAR NEG FORALL EXISTS FORALL2 FORALL3 EXISTS3 EXISTS2 IMPL IMPL2 IMPL3 IFF IFF2

%nonassoc IFF IFF2
%right IMPL IMPL2 IMPL3 
%left AND AND2 OR BAR
%left NEG

  /* The boolean value */
%token TRUE FALSE

  /* parenthese */
%token LPAREN RPAREN
%token LBRACK RBRACK

  /* ponctuation */
%token COMMA DOT LT SPASS SEMICOLON



%start input
%type <unit> input

%% /* Grammar rules and actions follow */

  input:    

| formula SEMICOLON input {
    
    resolve_formula $1;

  }

| LBRACK listterm listterm RBRACK input {

    printf "("; print_list_term $2; printf ") & ("; print_list_term $3; printf ") => ";
    match (unification_listterm $2 $3) with
      | None -> printf "Pas d'unification!!\n";
      | Some s -> 
          printf "Unification possible:\n "; print_subs (comp_subs s); printf "\n";
          print_list_term (apply_subs_listterm $2 (comp_subs s)); printf " = "; print_list_term (apply_subs_listterm $3 (comp_subs s)); printf "\n";     

  }

| LBRACK LBRACK listterm listterm RBRACK RBRACK input {

    printf "("; print_list_term $3; printf ") & ("; print_list_term $4; printf ") => ";
    match (subsum_listterm $3 $4) with
      | None -> printf "Pas d'unification!!\n";
      | Some s -> 
          printf "Unification possible:\n "; print_subs s; printf "\n";
          print_list_term (apply_subs_listterm $3 (comp_subs s)); printf " = "; print_list_term $4; printf "\n";     

  }


| LBRACK clause RBRACK LT LBRACK clause RBRACK input {
    printf "[ "; print_cnf_lvl1 $2; printf " ] < [ "; print_cnf_lvl1 $6; printf " ] ?? \n";
    printf "%b\n" (subsum_clause_clause $2 $6);
  }

| LBRACK cnf RBRACK input {
    printf "[ "; print_cnf_lvl0 $2; printf " ] -> \n";
    printf "[ "; print_cnf_lvl0 (simpl_cnf_subsum $2 []); printf " ] \n\n";
  }

| SPASS formula {

    print_formula_spass $2; printf "\n\n";
    
  }

| LBRACK LBRACK cnf RBRACK RBRACK input {

    let f = (rename_used_var_lvl0 VarSet.empty $3 0) in
      let f1 = (simpl_cnf_subsum f []) in 
        
      (
        printf "Final: "; print_cnf_lvl0 f1; printf "\n\n";
        printf "nb clauses: %d\n" (List.length f1);        
        printf "-----------------------------------\n\n";
        printf "resolution found empty clause ?: "; (resolution f1 [] 0); printf "\n\n";

      )
  }

| EOF {}
  ;               

  formula:        
| FORALL NAME DOT formula { Forallf ($2, $4)}
| EXISTS NAME DOT formula { Existsf ($2, $4)}
| FORALL listname DOT formula { listname2Forallf $2 $4}
| EXISTS listname DOT formula { listname2Existsf $2 $4}
| FORALL2 NAME DOT formula { Forallf ($2, $4)}
| EXISTS2 NAME DOT formula { Existsf ($2, $4)}
| FORALL2 listname DOT formula { listname2Forallf $2 $4}
| EXISTS2 listname DOT formula { listname2Existsf $2 $4}
| FORALL3 NAME DOT formula { Forallf ($2, $4)}
| EXISTS3 NAME DOT formula { Existsf ($2, $4)}
| FORALL3 listname DOT formula { listname2Forallf $2 $4}
| EXISTS3 listname DOT formula { listname2Existsf $2 $4}
| formula IFF2 formula { Equiv ($1, $3) }
| formula IFF formula { Equiv ($1, $3) }
| formula IMPL formula {Implf ($1, $3)}
| formula IMPL2 formula {Implf ($1, $3)}
| formula IMPL3 formula {Implf ($1, $3)}
| formula AND formula {Andf ($1, $3)}
| formula AND2 formula {Andf ($1, $3)}
| formula OR formula {Orf ($1, $3)}
| formula BAR formula {Orf ($1, $3)}
| NEG formula {Negf $2}
| NAME LPAREN listterm RPAREN { Relf ($1, $3)}
| NAME LPAREN RPAREN { Relf ($1, [])}
| NAME LBRACK listterm RBRACK { Relf ($1, $3)}
| NAME LBRACK RBRACK { Relf ($1, [])}
| NAME { Relf ($1, [])}
| LPAREN formula RPAREN {$2}
  ;

  listterm:       
| NAME {(Vart $1) :: []}
| NAME LPAREN listterm RPAREN {(Fctt ($1, $3)) :: []}
| NAME LPAREN RPAREN {(Fctt ($1, [])) :: []}
| listterm COMMA listterm {$1 @ $3}
| LPAREN listterm RPAREN {$2}
  ;

  cnf:
| clause {$1 :: []}
| clause AND cnf {$1::[] @ $3}
| LPAREN cnf RPAREN {$2}
;

  clause:
| literal {$1}
| literal OR clause {$1 @ $3}
| LPAREN clause RPAREN {$2}
  ;

  literal:
| NAME LPAREN listterm RPAREN {(false, $1, $3) :: []}
| NAME LPAREN RPAREN {(false, $1, []) :: []}
| NEG NAME LPAREN listterm RPAREN {(true, $2, $4) :: []}
| NEG NAME LPAREN RPAREN {(true, $2, []) :: []}
| LPAREN literal RPAREN {$2}
  ;

 listname:
| NAME { $1 :: [] }    
| NAME listname { $1 :: $2}
 ;
