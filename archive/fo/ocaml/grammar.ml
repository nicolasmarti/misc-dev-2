type token =
  | NEWLINE
  | EOF
  | NAME of (string)
  | AND
  | AND2
  | OR
  | BAR
  | NEG
  | FORALL
  | EXISTS
  | FORALL2
  | FORALL3
  | EXISTS3
  | EXISTS2
  | IMPL
  | IMPL2
  | IMPL3
  | IFF
  | IFF2
  | TRUE
  | FALSE
  | LPAREN
  | RPAREN
  | LBRACK
  | RBRACK
  | COMMA
  | DOT
  | LT
  | SPASS
  | SEMICOLON

open Parsing;;
# 3 "grammar.mly"
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

# 93 "grammar.ml"
let yytransl_const = [|
  257 (* NEWLINE *);
    0 (* EOF *);
  259 (* AND *);
  260 (* AND2 *);
  261 (* OR *);
  262 (* BAR *);
  263 (* NEG *);
  264 (* FORALL *);
  265 (* EXISTS *);
  266 (* FORALL2 *);
  267 (* FORALL3 *);
  268 (* EXISTS3 *);
  269 (* EXISTS2 *);
  270 (* IMPL *);
  271 (* IMPL2 *);
  272 (* IMPL3 *);
  273 (* IFF *);
  274 (* IFF2 *);
  275 (* TRUE *);
  276 (* FALSE *);
  277 (* LPAREN *);
  278 (* RPAREN *);
  279 (* LBRACK *);
  280 (* RBRACK *);
  281 (* COMMA *);
  282 (* DOT *);
  283 (* LT *);
  284 (* SPASS *);
  285 (* SEMICOLON *);
    0|]

let yytransl_block = [|
  258 (* NAME *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\002\000\002\000\003\000\003\000\003\000\003\000\
\003\000\005\000\005\000\005\000\004\000\004\000\004\000\007\000\
\007\000\007\000\007\000\007\000\006\000\006\000\000\000"

let yylen = "\002\000\
\003\000\005\000\007\000\008\000\004\000\002\000\006\000\001\000\
\004\000\004\000\004\000\004\000\004\000\004\000\004\000\004\000\
\004\000\004\000\004\000\004\000\003\000\003\000\003\000\003\000\
\003\000\003\000\003\000\003\000\003\000\002\000\004\000\003\000\
\004\000\003\000\001\000\003\000\001\000\004\000\003\000\003\000\
\003\000\001\000\003\000\003\000\001\000\003\000\003\000\004\000\
\003\000\005\000\004\000\003\000\001\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\008\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\055\000\000\000\
\000\000\000\000\030\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\032\000\000\000\034\000\
\000\000\000\000\000\000\054\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\036\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\026\000\
\027\000\028\000\029\000\000\000\000\000\000\000\000\000\000\000\
\001\000\000\000\031\000\033\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\041\000\047\000\044\000\052\000\000\000\
\000\000\000\000\000\000\000\000\000\000\043\000\000\000\005\000\
\000\000\046\000\039\000\000\000\000\000\051\000\000\000\000\000\
\000\000\002\000\000\000\000\000\000\000\038\000\050\000\000\000\
\007\000\049\000\000\000\000\000\003\000\048\000\000\000\004\000"

let yydgoto = "\002\000\
\015\000\016\000\075\000\076\000\077\000\060\000\040\000"

let yysindex = "\035\000\
\062\000\000\000\000\000\239\254\188\255\048\255\063\255\073\255\
\093\255\100\255\106\255\188\255\092\255\188\255\000\000\115\255\
\095\255\067\255\000\000\006\255\084\255\008\255\088\255\014\255\
\096\255\018\255\098\255\019\255\123\255\020\255\158\255\171\255\
\105\255\202\255\200\255\200\255\017\255\087\255\182\255\207\255\
\211\255\188\255\188\255\188\255\188\255\188\255\188\255\188\255\
\188\255\188\255\062\000\192\255\003\255\000\000\079\255\000\000\
\167\255\238\255\188\255\000\000\188\255\188\255\188\255\188\255\
\188\255\188\255\188\255\188\255\188\255\188\255\188\255\000\000\
\144\255\225\255\125\255\046\255\226\255\189\255\017\255\244\255\
\228\255\003\255\194\255\201\255\222\255\062\000\203\255\000\000\
\000\000\000\000\000\000\227\255\227\255\227\255\227\255\227\255\
\000\000\146\255\000\000\000\000\211\255\211\255\211\255\211\255\
\211\255\211\255\211\255\211\255\211\255\211\255\211\255\211\255\
\000\000\198\255\149\255\000\000\000\000\000\000\000\000\220\255\
\229\255\230\255\062\000\233\255\201\255\000\000\234\255\000\000\
\203\255\000\000\000\000\212\255\000\000\000\000\213\255\232\255\
\062\000\000\000\151\255\203\255\236\255\000\000\000\000\062\000\
\000\000\000\000\214\255\235\255\000\000\000\000\062\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\062\255\000\000\000\000\000\000\000\000\000\000\000\000\103\255\
\250\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\031\255\000\000\000\000\000\000\000\000\
\000\000\239\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\248\255\000\000\037\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\003\000\009\000\011\000\012\000\013\000\
\000\000\000\000\000\000\000\000\014\000\015\000\017\000\023\000\
\025\000\026\000\027\000\028\000\029\000\031\000\037\000\039\000\
\049\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\061\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\055\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\205\255\093\000\030\000\250\255\005\000\172\000\223\255"

let yytablesize = 346
let yytable = "\097\000\
\035\000\078\000\023\000\017\000\052\000\018\000\038\000\058\000\
\024\000\058\000\025\000\022\000\021\000\009\000\011\000\058\000\
\010\000\039\000\052\000\058\000\058\000\058\000\012\000\053\000\
\013\000\015\000\017\000\019\000\018\000\080\000\020\000\059\000\
\037\000\062\000\128\000\001\000\014\000\053\000\016\000\064\000\
\081\000\082\000\037\000\066\000\068\000\070\000\055\000\057\000\
\084\000\020\000\039\000\049\000\037\000\049\000\037\000\037\000\
\038\000\048\000\042\000\048\000\042\000\003\000\040\000\037\000\
\022\000\079\000\083\000\117\000\052\000\039\000\039\000\138\000\
\049\000\039\000\024\000\038\000\038\000\080\000\048\000\038\000\
\130\000\040\000\040\000\037\000\040\000\145\000\037\000\053\000\
\126\000\084\000\056\000\078\000\149\000\033\000\026\000\078\000\
\052\000\019\000\034\000\152\000\099\000\028\000\114\000\082\000\
\032\000\045\000\041\000\030\000\120\000\061\000\085\000\122\000\
\035\000\063\000\036\000\053\000\054\000\042\000\043\000\044\000\
\045\000\065\000\141\000\067\000\045\000\073\000\045\000\132\000\
\046\000\047\000\048\000\049\000\050\000\148\000\088\000\089\000\
\090\000\091\000\092\000\093\000\094\000\095\000\096\000\051\000\
\135\000\052\000\116\000\052\000\069\000\082\000\052\000\101\000\
\052\000\102\000\103\000\104\000\105\000\106\000\107\000\108\000\
\109\000\110\000\111\000\112\000\053\000\113\000\053\000\131\000\
\147\000\053\000\134\000\053\000\146\000\042\000\043\000\044\000\
\045\000\021\000\023\000\025\000\027\000\029\000\031\000\071\000\
\046\000\047\000\048\000\049\000\050\000\004\000\100\000\082\000\
\072\000\087\000\005\000\006\000\007\000\008\000\009\000\010\000\
\011\000\033\000\124\000\074\000\124\000\086\000\034\000\034\000\
\012\000\034\000\119\000\087\000\098\000\042\000\043\000\044\000\
\045\000\123\000\082\000\133\000\035\000\125\000\082\000\129\000\
\046\000\047\000\048\000\049\000\050\000\042\000\043\000\044\000\
\045\000\142\000\143\000\150\000\082\000\082\000\082\000\058\000\
\046\000\047\000\048\000\136\000\082\000\115\000\084\000\118\000\
\127\000\006\000\045\000\121\000\137\000\139\000\082\000\144\000\
\140\000\117\000\151\000\035\000\035\000\035\000\035\000\000\000\
\053\000\000\000\000\000\000\000\000\000\000\000\035\000\035\000\
\035\000\035\000\035\000\023\000\023\000\000\000\035\000\000\000\
\023\000\024\000\024\000\025\000\025\000\035\000\024\000\023\000\
\025\000\022\000\021\000\009\000\011\000\024\000\010\000\025\000\
\022\000\021\000\009\000\011\000\012\000\010\000\013\000\015\000\
\017\000\019\000\018\000\012\000\020\000\013\000\015\000\017\000\
\019\000\018\000\014\000\020\000\016\000\000\000\000\000\004\000\
\000\000\014\000\000\000\016\000\005\000\006\000\007\000\008\000\
\009\000\010\000\011\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\012\000\000\000\013\000\000\000\000\000\000\000\
\000\000\014\000"

let yycheck = "\051\000\
\000\000\035\000\000\000\021\001\002\001\023\001\013\000\002\001\
\000\000\002\001\000\000\000\000\000\000\000\000\000\000\002\001\
\000\000\013\000\002\001\002\001\002\001\002\001\000\000\021\001\
\000\000\000\000\000\000\000\000\000\000\036\000\000\000\026\001\
\002\001\026\001\086\000\001\000\000\000\021\001\000\000\026\001\
\036\000\025\001\013\000\026\001\026\001\026\001\017\000\018\000\
\003\001\002\001\002\001\003\001\022\001\005\001\024\001\025\001\
\002\001\003\001\022\001\005\001\024\001\000\000\002\001\002\001\
\002\001\036\000\037\000\022\001\002\001\021\001\022\001\123\000\
\024\001\025\001\002\001\021\001\022\001\084\000\024\001\025\001\
\087\000\021\001\022\001\022\001\024\001\137\000\025\001\021\001\
\084\000\003\001\024\001\125\000\144\000\002\001\002\001\129\000\
\002\001\005\000\007\001\151\000\022\001\002\001\073\000\025\001\
\012\000\003\001\014\000\002\001\079\000\026\001\024\001\082\000\
\021\001\026\001\023\001\021\001\022\001\003\001\004\001\005\001\
\006\001\026\001\129\000\026\001\022\001\021\001\024\001\098\000\
\014\001\015\001\016\001\017\001\018\001\140\000\042\000\043\000\
\044\000\045\000\046\000\047\000\048\000\049\000\050\000\029\001\
\115\000\002\001\022\001\002\001\026\001\025\001\002\001\059\000\
\002\001\061\000\062\000\063\000\064\000\065\000\066\000\067\000\
\068\000\069\000\070\000\071\000\021\001\022\001\021\001\022\001\
\139\000\021\001\022\001\021\001\022\001\003\001\004\001\005\001\
\006\001\006\000\007\000\008\000\009\000\010\000\011\000\026\001\
\014\001\015\001\016\001\017\001\018\001\002\001\024\001\025\001\
\022\001\005\001\007\001\008\001\009\001\010\001\011\001\012\001\
\013\001\002\001\002\001\002\001\002\001\024\001\007\001\007\001\
\021\001\007\001\022\001\005\001\021\001\003\001\004\001\005\001\
\006\001\024\001\025\001\022\001\021\001\021\001\025\001\021\001\
\014\001\015\001\016\001\017\001\018\001\003\001\004\001\005\001\
\006\001\022\001\022\001\022\001\025\001\025\001\025\001\002\001\
\014\001\015\001\016\001\024\001\025\001\021\001\003\001\022\001\
\027\001\000\000\003\001\024\001\024\001\021\001\025\001\024\001\
\023\001\022\001\024\001\003\001\004\001\005\001\006\001\255\255\
\026\001\255\255\255\255\255\255\255\255\255\255\014\001\015\001\
\016\001\017\001\018\001\017\001\018\001\255\255\022\001\255\255\
\022\001\017\001\018\001\017\001\018\001\029\001\022\001\029\001\
\022\001\022\001\022\001\022\001\022\001\029\001\022\001\029\001\
\029\001\029\001\029\001\029\001\022\001\029\001\022\001\022\001\
\022\001\022\001\022\001\029\001\022\001\029\001\029\001\029\001\
\029\001\029\001\022\001\029\001\022\001\255\255\255\255\002\001\
\255\255\029\001\255\255\029\001\007\001\008\001\009\001\010\001\
\011\001\012\001\013\001\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\021\001\255\255\023\001\255\255\255\255\255\255\
\255\255\028\001"

let yynames_const = "\
  NEWLINE\000\
  EOF\000\
  AND\000\
  AND2\000\
  OR\000\
  BAR\000\
  NEG\000\
  FORALL\000\
  EXISTS\000\
  FORALL2\000\
  FORALL3\000\
  EXISTS3\000\
  EXISTS2\000\
  IMPL\000\
  IMPL2\000\
  IMPL3\000\
  IFF\000\
  IFF2\000\
  TRUE\000\
  FALSE\000\
  LPAREN\000\
  RPAREN\000\
  LBRACK\000\
  RBRACK\000\
  COMMA\000\
  DOT\000\
  LT\000\
  SPASS\000\
  SEMICOLON\000\
  "

let yynames_block = "\
  NAME\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : unit) in
    Obj.repr(
# 95 "grammar.mly"
                          (
    
    resolve_formula _1;

  )
# 358 "grammar.ml"
               : unit))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'listterm) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'listterm) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : unit) in
    Obj.repr(
# 101 "grammar.mly"
                                        (

    printf "("; print_list_term _2; printf ") & ("; print_list_term _3; printf ") => ";
    match (unification_listterm _2 _3) with
      | None -> printf "Pas d'unification!!\n";
      | Some s -> 
          printf "Unification possible:\n "; print_subs (comp_subs s); printf "\n";
          print_list_term (apply_subs_listterm _2 (comp_subs s)); printf " = "; print_list_term (apply_subs_listterm _3 (comp_subs s)); printf "\n";     

  )
# 376 "grammar.ml"
               : unit))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'listterm) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : 'listterm) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : unit) in
    Obj.repr(
# 112 "grammar.mly"
                                                      (

    printf "("; print_list_term _3; printf ") & ("; print_list_term _4; printf ") => ";
    match (subsum_listterm _3 _4) with
      | None -> printf "Pas d'unification!!\n";
      | Some s -> 
          printf "Unification possible:\n "; print_subs s; printf "\n";
          print_list_term (apply_subs_listterm _3 (comp_subs s)); printf " = "; print_list_term _4; printf "\n";     

  )
# 394 "grammar.ml"
               : unit))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : 'clause) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'clause) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : unit) in
    Obj.repr(
# 124 "grammar.mly"
                                                     (
    printf "[ "; print_cnf_lvl1 _2; printf " ] < [ "; print_cnf_lvl1 _6; printf " ] ?? \n";
    printf "%b\n" (subsum_clause_clause _2 _6);
  )
# 406 "grammar.ml"
               : unit))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'cnf) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : unit) in
    Obj.repr(
# 129 "grammar.mly"
                          (
    printf "[ "; print_cnf_lvl0 _2; printf " ] -> \n";
    printf "[ "; print_cnf_lvl0 (simpl_cnf_subsum _2 []); printf " ] \n\n";
  )
# 417 "grammar.ml"
               : unit))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 134 "grammar.mly"
                (

    print_formula_spass _2; printf "\n\n";
    
  )
# 428 "grammar.ml"
               : unit))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'cnf) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : unit) in
    Obj.repr(
# 140 "grammar.mly"
                                        (

    let f = (rename_used_var_lvl0 VarSet.empty _3 0) in
      let f1 = (simpl_cnf_subsum f []) in 
        
      (
        printf "Final: "; print_cnf_lvl0 f1; printf "\n\n";
        printf "nb clauses: %d\n" (List.length f1);        
        printf "-----------------------------------\n\n";
        printf "resolution found empty clause ?: "; (resolution f1 [] 0); printf "\n\n";

      )
  )
# 448 "grammar.ml"
               : unit))
; (fun __caml_parser_env ->
    Obj.repr(
# 154 "grammar.mly"
      ()
# 454 "grammar.ml"
               : unit))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 158 "grammar.mly"
                          ( Forallf (_2, _4))
# 462 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 159 "grammar.mly"
                          ( Existsf (_2, _4))
# 470 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'listname) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 160 "grammar.mly"
                              ( listname2Forallf _2 _4)
# 478 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'listname) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 161 "grammar.mly"
                              ( listname2Existsf _2 _4)
# 486 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 162 "grammar.mly"
                           ( Forallf (_2, _4))
# 494 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 163 "grammar.mly"
                           ( Existsf (_2, _4))
# 502 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'listname) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 164 "grammar.mly"
                               ( listname2Forallf _2 _4)
# 510 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'listname) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 165 "grammar.mly"
                               ( listname2Existsf _2 _4)
# 518 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 166 "grammar.mly"
                           ( Forallf (_2, _4))
# 526 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 167 "grammar.mly"
                           ( Existsf (_2, _4))
# 534 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'listname) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 168 "grammar.mly"
                               ( listname2Forallf _2 _4)
# 542 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'listname) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 169 "grammar.mly"
                               ( listname2Existsf _2 _4)
# 550 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 170 "grammar.mly"
                       ( Equiv (_1, _3) )
# 558 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 171 "grammar.mly"
                      ( Equiv (_1, _3) )
# 566 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 172 "grammar.mly"
                       (Implf (_1, _3))
# 574 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 173 "grammar.mly"
                        (Implf (_1, _3))
# 582 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 174 "grammar.mly"
                        (Implf (_1, _3))
# 590 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 175 "grammar.mly"
                      (Andf (_1, _3))
# 598 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 176 "grammar.mly"
                       (Andf (_1, _3))
# 606 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 177 "grammar.mly"
                     (Orf (_1, _3))
# 614 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 178 "grammar.mly"
                      (Orf (_1, _3))
# 622 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 179 "grammar.mly"
              (Negf _2)
# 629 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'listterm) in
    Obj.repr(
# 180 "grammar.mly"
                              ( Relf (_1, _3))
# 637 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 181 "grammar.mly"
                     ( Relf (_1, []))
# 644 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'listterm) in
    Obj.repr(
# 182 "grammar.mly"
                              ( Relf (_1, _3))
# 652 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 183 "grammar.mly"
                     ( Relf (_1, []))
# 659 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 184 "grammar.mly"
       ( Relf (_1, []))
# 666 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'formula) in
    Obj.repr(
# 185 "grammar.mly"
                        (_2)
# 673 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 189 "grammar.mly"
       ((Vart _1) :: [])
# 680 "grammar.ml"
               : 'listterm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'listterm) in
    Obj.repr(
# 190 "grammar.mly"
                              ((Fctt (_1, _3)) :: [])
# 688 "grammar.ml"
               : 'listterm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 191 "grammar.mly"
                     ((Fctt (_1, [])) :: [])
# 695 "grammar.ml"
               : 'listterm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'listterm) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'listterm) in
    Obj.repr(
# 192 "grammar.mly"
                          (_1 @ _3)
# 703 "grammar.ml"
               : 'listterm))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'listterm) in
    Obj.repr(
# 193 "grammar.mly"
                         (_2)
# 710 "grammar.ml"
               : 'listterm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'clause) in
    Obj.repr(
# 197 "grammar.mly"
         (_1 :: [])
# 717 "grammar.ml"
               : 'cnf))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'clause) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cnf) in
    Obj.repr(
# 198 "grammar.mly"
                 (_1::[] @ _3)
# 725 "grammar.ml"
               : 'cnf))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'cnf) in
    Obj.repr(
# 199 "grammar.mly"
                    (_2)
# 732 "grammar.ml"
               : 'cnf))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'literal) in
    Obj.repr(
# 203 "grammar.mly"
          (_1)
# 739 "grammar.ml"
               : 'clause))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'literal) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'clause) in
    Obj.repr(
# 204 "grammar.mly"
                    (_1 @ _3)
# 747 "grammar.ml"
               : 'clause))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'clause) in
    Obj.repr(
# 205 "grammar.mly"
                       (_2)
# 754 "grammar.ml"
               : 'clause))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'listterm) in
    Obj.repr(
# 209 "grammar.mly"
                              ((false, _1, _3) :: [])
# 762 "grammar.ml"
               : 'literal))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 210 "grammar.mly"
                     ((false, _1, []) :: [])
# 769 "grammar.ml"
               : 'literal))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'listterm) in
    Obj.repr(
# 211 "grammar.mly"
                                  ((true, _2, _4) :: [])
# 777 "grammar.ml"
               : 'literal))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 212 "grammar.mly"
                         ((true, _2, []) :: [])
# 784 "grammar.ml"
               : 'literal))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'literal) in
    Obj.repr(
# 213 "grammar.mly"
                        (_2)
# 791 "grammar.ml"
               : 'literal))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 217 "grammar.mly"
       ( _1 :: [] )
# 798 "grammar.ml"
               : 'listname))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'listname) in
    Obj.repr(
# 218 "grammar.mly"
                ( _1 :: _2)
# 806 "grammar.ml"
               : 'listname))
(* Entry input *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let input (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : unit)
