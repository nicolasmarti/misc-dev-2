type token =
  | NEWLINE
  | EOF
  | NAME of (string)
  | AND
  | OR
  | NEG
  | FORALL
  | EXISTS
  | FORALL2
  | EXISTS2
  | IMPL
  | IMPL2
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
  | BAR
  | LT
  | SPASS

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
    printf "\n\n***********************************\n\n";
    printf "formula f:\n"; print_formula f; printf "\n\n"; 
    (*printf "SPASS :\n"; print_formula_spass f; printf "\n\n";*)
    printf "-----------------------------------\n\n";
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
          printf "Final: "; print_cnf_lvl0 (List.sort clause_compare f10); printf "\n\n";
          printf "nb clauses: %d\n" (List.length f10);        
          printf "resolution2 found empty clause ?: \n"; flush stdout;
          (resolution2 (List.sort clause_compare f10) [] 1); printf "\n\n"; flush stdout;
          printf "resolution found empty clause ?: "; flush stdout;
          (resolution (List.sort clause_compare f10) [] 1); printf "\n\n"; flush stdout;
          printf "-----------------------------------\n\n";;

# 86 "grammar.ml"
let yytransl_const = [|
  257 (* NEWLINE *);
    0 (* EOF *);
  259 (* AND *);
  260 (* OR *);
  261 (* NEG *);
  262 (* FORALL *);
  263 (* EXISTS *);
  264 (* FORALL2 *);
  265 (* EXISTS2 *);
  266 (* IMPL *);
  267 (* IMPL2 *);
  268 (* IFF *);
  269 (* IFF2 *);
  270 (* TRUE *);
  271 (* FALSE *);
  272 (* LPAREN *);
  273 (* RPAREN *);
  274 (* LBRACK *);
  275 (* RBRACK *);
  276 (* COMMA *);
  277 (* DOT *);
  278 (* BAR *);
  279 (* LT *);
  280 (* SPASS *);
    0|]

let yytransl_block = [|
  258 (* NAME *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\002\000\002\000\002\000\003\000\003\000\003\000\
\003\000\003\000\005\000\005\000\005\000\004\000\004\000\004\000\
\007\000\007\000\007\000\007\000\007\000\006\000\006\000\000\000"

let yylen = "\002\000\
\002\000\005\000\007\000\008\000\004\000\002\000\006\000\001\000\
\004\000\004\000\004\000\004\000\004\000\004\000\004\000\004\000\
\003\000\003\000\003\000\003\000\003\000\003\000\002\000\004\000\
\003\000\004\000\003\000\001\000\003\000\001\000\004\000\003\000\
\003\000\003\000\001\000\003\000\003\000\001\000\003\000\003\000\
\004\000\003\000\005\000\004\000\003\000\001\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\008\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\048\000\000\000\000\000\000\000\
\023\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\001\000\000\000\000\000\025\000\000\000\027\000\000\000\
\000\000\000\000\047\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\029\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\021\000\022\000\000\000\000\000\000\000\000\000\
\000\000\024\000\026\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\034\000\040\000\
\037\000\045\000\000\000\000\000\000\000\000\000\000\000\000\000\
\036\000\000\000\005\000\000\000\039\000\032\000\000\000\000\000\
\044\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\
\031\000\043\000\000\000\007\000\042\000\000\000\000\000\003\000\
\041\000\000\000\004\000"

let yydgoto = "\002\000\
\013\000\014\000\062\000\063\000\064\000\051\000\034\000"

let yysindex = "\006\000\
\021\001\000\000\000\000\148\255\143\255\047\255\079\255\103\255\
\109\255\143\255\085\255\143\255\000\000\001\000\003\255\056\255\
\000\000\002\255\110\255\007\255\126\255\010\255\135\255\011\255\
\154\255\150\255\156\255\188\255\078\255\078\255\020\255\081\255\
\176\255\192\255\170\255\143\255\143\255\143\255\143\255\143\255\
\143\255\000\000\182\255\014\255\000\000\253\254\000\000\066\255\
\197\255\143\255\000\000\143\255\143\255\143\255\143\255\143\255\
\143\255\143\255\000\000\090\255\184\255\254\254\129\255\185\255\
\104\255\020\255\198\255\186\255\014\255\151\255\153\255\180\255\
\021\001\163\255\000\000\000\000\181\255\181\255\181\255\181\255\
\102\255\000\000\000\000\170\255\170\255\170\255\170\255\170\255\
\170\255\170\255\170\255\000\000\021\255\112\255\000\000\000\000\
\000\000\000\000\174\255\187\255\189\255\021\001\191\255\153\255\
\000\000\190\255\000\000\163\255\000\000\000\000\022\255\000\000\
\000\000\095\255\193\255\021\001\000\000\118\255\163\255\194\255\
\000\000\000\000\021\001\000\000\000\000\113\255\195\255\000\000\
\000\000\021\001\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\024\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\043\255\000\000\000\000\000\000\000\000\000\000\
\000\000\076\255\204\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\054\255\000\000\000\000\000\000\000\000\000\000\
\199\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\207\255\000\000\159\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\037\000\057\000\077\000\097\000\
\000\000\000\000\000\000\117\000\137\000\157\000\177\000\197\000\
\217\000\237\000\001\001\031\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\027\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\050\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000"

let yygindex = "\000\000\
\242\255\086\000\251\255\247\255\253\255\180\000\230\255"

let yytablesize = 557
let yytable = "\042\000\
\003\000\032\000\065\000\049\000\043\000\031\000\001\000\033\000\
\049\000\046\000\048\000\049\000\049\000\082\000\095\000\043\000\
\069\000\069\000\044\000\045\000\067\000\043\000\050\000\028\000\
\066\000\070\000\068\000\053\000\033\000\044\000\055\000\057\000\
\032\000\042\000\042\000\044\000\019\000\112\000\121\000\069\000\
\069\000\069\000\033\000\033\000\030\000\033\000\032\000\032\000\
\018\000\042\000\032\000\031\000\041\000\041\000\093\000\030\000\
\020\000\043\000\107\000\030\000\099\000\067\000\030\000\101\000\
\109\000\031\000\031\000\105\000\041\000\031\000\030\000\044\000\
\030\000\030\000\047\000\111\000\018\000\065\000\038\000\027\000\
\020\000\065\000\028\000\071\000\083\000\069\000\027\000\117\000\
\114\000\028\000\017\000\043\000\038\000\029\000\038\000\026\000\
\017\000\035\000\120\000\072\000\029\000\124\000\030\000\043\000\
\022\000\044\000\092\000\074\000\128\000\127\000\024\000\122\000\
\126\000\043\000\069\000\131\000\009\000\044\000\110\000\043\000\
\098\000\075\000\076\000\077\000\078\000\079\000\080\000\044\000\
\113\000\129\000\052\000\071\000\069\000\044\000\125\000\084\000\
\011\000\085\000\086\000\087\000\088\000\089\000\090\000\091\000\
\004\000\096\000\054\000\005\000\006\000\007\000\008\000\009\000\
\036\000\037\000\103\000\056\000\010\000\028\000\010\000\038\000\
\039\000\040\000\041\000\015\000\103\000\016\000\059\000\028\000\
\104\000\102\000\069\000\060\000\036\000\037\000\058\000\035\000\
\012\000\035\000\108\000\038\000\039\000\040\000\041\000\036\000\
\037\000\019\000\021\000\023\000\025\000\061\000\038\000\039\000\
\115\000\069\000\073\000\074\000\013\000\081\000\049\000\094\000\
\071\000\097\000\106\000\006\000\100\000\116\000\118\000\119\000\
\069\000\038\000\096\000\123\000\000\000\130\000\000\000\000\000\
\015\000\000\000\000\000\046\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\014\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\016\000\000\000\004\000\036\000\037\000\005\000\006\000\007\000\
\008\000\009\000\038\000\039\000\040\000\041\000\000\000\000\000\
\010\000\000\000\011\000\000\000\003\000\000\000\000\000\000\000\
\012\000\028\000\028\000\028\000\028\000\028\000\028\000\028\000\
\028\000\028\000\028\000\028\000\028\000\000\000\019\000\000\000\
\028\000\019\000\019\000\019\000\019\000\019\000\000\000\028\000\
\019\000\019\000\000\000\000\000\019\000\019\000\019\000\000\000\
\000\000\000\000\020\000\000\000\019\000\020\000\020\000\020\000\
\020\000\020\000\000\000\000\000\020\000\020\000\000\000\000\000\
\020\000\020\000\020\000\000\000\000\000\000\000\018\000\000\000\
\020\000\018\000\018\000\018\000\018\000\018\000\000\000\000\000\
\000\000\000\000\000\000\000\000\018\000\018\000\018\000\000\000\
\000\000\000\000\017\000\000\000\018\000\017\000\017\000\017\000\
\017\000\017\000\000\000\000\000\000\000\000\000\000\000\000\000\
\017\000\017\000\017\000\000\000\000\000\000\000\009\000\000\000\
\017\000\009\000\009\000\009\000\009\000\009\000\000\000\000\000\
\000\000\000\000\000\000\000\000\009\000\009\000\009\000\000\000\
\000\000\000\000\011\000\000\000\009\000\011\000\011\000\011\000\
\011\000\011\000\000\000\000\000\000\000\000\000\000\000\000\000\
\011\000\011\000\011\000\000\000\000\000\000\000\010\000\000\000\
\011\000\010\000\010\000\010\000\010\000\010\000\000\000\000\000\
\000\000\000\000\000\000\000\000\010\000\010\000\010\000\000\000\
\000\000\000\000\012\000\000\000\010\000\012\000\012\000\012\000\
\012\000\012\000\000\000\000\000\000\000\000\000\000\000\000\000\
\012\000\012\000\012\000\000\000\000\000\000\000\013\000\000\000\
\012\000\013\000\013\000\013\000\013\000\013\000\000\000\000\000\
\000\000\000\000\000\000\000\000\013\000\013\000\013\000\000\000\
\000\000\000\000\015\000\000\000\013\000\015\000\015\000\015\000\
\015\000\015\000\000\000\000\000\000\000\000\000\000\000\000\000\
\015\000\015\000\015\000\000\000\000\000\000\000\014\000\000\000\
\015\000\014\000\014\000\014\000\014\000\014\000\000\000\000\000\
\000\000\000\000\000\000\000\000\014\000\014\000\014\000\000\000\
\000\000\000\000\016\000\000\000\014\000\016\000\016\000\016\000\
\016\000\016\000\000\000\000\000\000\000\000\000\000\000\000\000\
\016\000\016\000\016\000\000\000\000\000\000\000\004\000\000\000\
\016\000\005\000\006\000\007\000\008\000\009\000\000\000\000\000\
\000\000\000\000\000\000\000\000\010\000\000\000\011\000\000\000\
\000\000\000\000\000\000\000\000\012\000"

let yycheck = "\014\000\
\000\000\011\000\029\000\002\001\002\001\011\000\001\000\011\000\
\002\001\015\000\016\000\002\001\002\001\017\001\017\001\002\001\
\020\001\020\001\016\001\017\001\030\000\002\001\021\001\000\000\
\030\000\031\000\030\000\021\001\002\001\016\001\021\001\021\001\
\002\001\003\001\004\001\016\001\000\000\017\001\017\001\020\001\
\020\001\020\001\016\001\017\001\002\001\019\001\016\001\017\001\
\002\001\019\001\020\001\002\001\003\001\004\001\060\000\002\001\
\000\000\002\001\073\000\017\001\066\000\071\000\020\001\069\000\
\074\000\016\001\017\001\071\000\019\001\020\001\017\001\016\001\
\019\001\020\001\019\001\081\000\000\000\104\000\003\001\002\001\
\002\001\108\000\005\001\003\001\019\001\020\001\002\001\102\000\
\094\000\005\001\005\000\002\001\017\001\016\001\019\001\010\000\
\000\000\012\000\108\000\019\001\016\001\116\000\018\001\002\001\
\002\001\016\001\017\001\004\001\123\000\119\000\002\001\017\001\
\118\000\002\001\020\001\130\000\000\000\016\001\017\001\002\001\
\017\001\036\000\037\000\038\000\039\000\040\000\041\000\016\001\
\017\001\017\001\021\001\003\001\020\001\016\001\017\001\050\000\
\000\000\052\000\053\000\054\000\055\000\056\000\057\000\058\000\
\002\001\017\001\021\001\005\001\006\001\007\001\008\001\009\001\
\003\001\004\001\002\001\021\001\000\000\005\001\016\001\010\001\
\011\001\012\001\013\001\016\001\002\001\018\001\017\001\005\001\
\016\001\019\001\020\001\016\001\003\001\004\001\021\001\017\001\
\000\000\019\001\016\001\010\001\011\001\012\001\013\001\003\001\
\004\001\006\000\007\000\008\000\009\000\002\001\010\001\011\001\
\019\001\020\001\019\001\004\001\000\000\016\001\002\001\016\001\
\003\001\017\001\023\001\000\000\019\001\019\001\016\001\018\001\
\020\001\003\001\017\001\019\001\255\255\019\001\255\255\255\255\
\000\000\255\255\255\255\021\001\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\000\000\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\000\000\255\255\002\001\003\001\004\001\005\001\006\001\007\001\
\008\001\009\001\010\001\011\001\012\001\013\001\255\255\255\255\
\016\001\255\255\018\001\255\255\000\000\255\255\255\255\255\255\
\024\001\002\001\003\001\004\001\005\001\006\001\007\001\008\001\
\009\001\010\001\011\001\012\001\013\001\255\255\002\001\255\255\
\017\001\005\001\006\001\007\001\008\001\009\001\255\255\024\001\
\012\001\013\001\255\255\255\255\016\001\017\001\018\001\255\255\
\255\255\255\255\002\001\255\255\024\001\005\001\006\001\007\001\
\008\001\009\001\255\255\255\255\012\001\013\001\255\255\255\255\
\016\001\017\001\018\001\255\255\255\255\255\255\002\001\255\255\
\024\001\005\001\006\001\007\001\008\001\009\001\255\255\255\255\
\255\255\255\255\255\255\255\255\016\001\017\001\018\001\255\255\
\255\255\255\255\002\001\255\255\024\001\005\001\006\001\007\001\
\008\001\009\001\255\255\255\255\255\255\255\255\255\255\255\255\
\016\001\017\001\018\001\255\255\255\255\255\255\002\001\255\255\
\024\001\005\001\006\001\007\001\008\001\009\001\255\255\255\255\
\255\255\255\255\255\255\255\255\016\001\017\001\018\001\255\255\
\255\255\255\255\002\001\255\255\024\001\005\001\006\001\007\001\
\008\001\009\001\255\255\255\255\255\255\255\255\255\255\255\255\
\016\001\017\001\018\001\255\255\255\255\255\255\002\001\255\255\
\024\001\005\001\006\001\007\001\008\001\009\001\255\255\255\255\
\255\255\255\255\255\255\255\255\016\001\017\001\018\001\255\255\
\255\255\255\255\002\001\255\255\024\001\005\001\006\001\007\001\
\008\001\009\001\255\255\255\255\255\255\255\255\255\255\255\255\
\016\001\017\001\018\001\255\255\255\255\255\255\002\001\255\255\
\024\001\005\001\006\001\007\001\008\001\009\001\255\255\255\255\
\255\255\255\255\255\255\255\255\016\001\017\001\018\001\255\255\
\255\255\255\255\002\001\255\255\024\001\005\001\006\001\007\001\
\008\001\009\001\255\255\255\255\255\255\255\255\255\255\255\255\
\016\001\017\001\018\001\255\255\255\255\255\255\002\001\255\255\
\024\001\005\001\006\001\007\001\008\001\009\001\255\255\255\255\
\255\255\255\255\255\255\255\255\016\001\017\001\018\001\255\255\
\255\255\255\255\002\001\255\255\024\001\005\001\006\001\007\001\
\008\001\009\001\255\255\255\255\255\255\255\255\255\255\255\255\
\016\001\017\001\018\001\255\255\255\255\255\255\002\001\255\255\
\024\001\005\001\006\001\007\001\008\001\009\001\255\255\255\255\
\255\255\255\255\255\255\255\255\016\001\255\255\018\001\255\255\
\255\255\255\255\255\255\255\255\024\001"

let yynames_const = "\
  NEWLINE\000\
  EOF\000\
  AND\000\
  OR\000\
  NEG\000\
  FORALL\000\
  EXISTS\000\
  FORALL2\000\
  EXISTS2\000\
  IMPL\000\
  IMPL2\000\
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
  BAR\000\
  LT\000\
  SPASS\000\
  "

let yynames_block = "\
  NAME\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'formula) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : unit) in
    Obj.repr(
# 93 "grammar.mly"
                (
    
    resolve_formula _1;

  )
# 385 "grammar.ml"
               : unit))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'listterm) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'listterm) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : unit) in
    Obj.repr(
# 99 "grammar.mly"
                                        (

    printf "("; print_list_term _2; printf ") & ("; print_list_term _3; printf ") => ";
    match (unification_listterm _2 _3) with
      | None -> printf "Pas d'unification!!\n";
      | Some s -> 
          printf "Unification possible:\n "; print_subs (comp_subs s); printf "\n";
          print_list_term (apply_subs_listterm _2 (comp_subs s)); printf " = "; print_list_term (apply_subs_listterm _3 (comp_subs s)); printf "\n";     

  )
# 403 "grammar.ml"
               : unit))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'listterm) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : 'listterm) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : unit) in
    Obj.repr(
# 110 "grammar.mly"
                                                      (

    printf "("; print_list_term _3; printf ") & ("; print_list_term _4; printf ") => ";
    match (subsum_listterm _3 _4) with
      | None -> printf "Pas d'unification!!\n";
      | Some s -> 
          printf "Unification possible:\n "; print_subs s; printf "\n";
          print_list_term (apply_subs_listterm _3 (comp_subs s)); printf " = "; print_list_term _4; printf "\n";     

  )
# 421 "grammar.ml"
               : unit))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : 'clause) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'clause) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : unit) in
    Obj.repr(
# 122 "grammar.mly"
                                                     (
    printf "[ "; print_cnf_lvl1 _2; printf " ] < [ "; print_cnf_lvl1 _6; printf " ] ?? \n";
    printf "%b\n" (subsum_clause_clause _2 _6);
  )
# 433 "grammar.ml"
               : unit))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'cnf) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : unit) in
    Obj.repr(
# 127 "grammar.mly"
                          (
    printf "[ "; print_cnf_lvl0 _2; printf " ] -> \n";
    printf "[ "; print_cnf_lvl0 (simpl_cnf_subsum _2 []); printf " ] \n\n";
  )
# 444 "grammar.ml"
               : unit))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 132 "grammar.mly"
                (

    print_formula_spass _2; printf "\n\n";
    
  )
# 455 "grammar.ml"
               : unit))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'cnf) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : unit) in
    Obj.repr(
# 138 "grammar.mly"
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
# 475 "grammar.ml"
               : unit))
; (fun __caml_parser_env ->
    Obj.repr(
# 152 "grammar.mly"
      ()
# 481 "grammar.ml"
               : unit))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 156 "grammar.mly"
                          ( Forallf (_2, _4))
# 489 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 157 "grammar.mly"
                          ( Existsf (_2, _4))
# 497 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'listname) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 158 "grammar.mly"
                              ( listname2Forallf _2 _4)
# 505 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'listname) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 159 "grammar.mly"
                              ( listname2Existsf _2 _4)
# 513 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 160 "grammar.mly"
                           ( Forallf (_2, _4))
# 521 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 161 "grammar.mly"
                           ( Existsf (_2, _4))
# 529 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'listname) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 162 "grammar.mly"
                               ( listname2Forallf _2 _4)
# 537 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'listname) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 163 "grammar.mly"
                               ( listname2Existsf _2 _4)
# 545 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 164 "grammar.mly"
                       ( Equiv (_1, _3) )
# 553 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 165 "grammar.mly"
                      ( Equiv (_1, _3) )
# 561 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 166 "grammar.mly"
                       (Implf (_1, _3))
# 569 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 167 "grammar.mly"
                        (Implf (_1, _3))
# 577 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 168 "grammar.mly"
                      (Andf (_1, _3))
# 585 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 169 "grammar.mly"
                     (Orf (_1, _3))
# 593 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 170 "grammar.mly"
              (Negf _2)
# 600 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'listterm) in
    Obj.repr(
# 171 "grammar.mly"
                              ( Relf (_1, _3))
# 608 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 172 "grammar.mly"
                     ( Relf (_1, []))
# 615 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'listterm) in
    Obj.repr(
# 173 "grammar.mly"
                              ( Relf (_1, _3))
# 623 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 174 "grammar.mly"
                     ( Relf (_1, []))
# 630 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 175 "grammar.mly"
       ( Relf (_1, []))
# 637 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'formula) in
    Obj.repr(
# 176 "grammar.mly"
                        (_2)
# 644 "grammar.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 180 "grammar.mly"
       ((Vart _1) :: [])
# 651 "grammar.ml"
               : 'listterm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'listterm) in
    Obj.repr(
# 181 "grammar.mly"
                              ((Fctt (_1, _3)) :: [])
# 659 "grammar.ml"
               : 'listterm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 182 "grammar.mly"
                     ((Fctt (_1, [])) :: [])
# 666 "grammar.ml"
               : 'listterm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'listterm) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'listterm) in
    Obj.repr(
# 183 "grammar.mly"
                          (_1 @ _3)
# 674 "grammar.ml"
               : 'listterm))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'listterm) in
    Obj.repr(
# 184 "grammar.mly"
                         (_2)
# 681 "grammar.ml"
               : 'listterm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'clause) in
    Obj.repr(
# 188 "grammar.mly"
         (_1 :: [])
# 688 "grammar.ml"
               : 'cnf))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'clause) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cnf) in
    Obj.repr(
# 189 "grammar.mly"
                 (_1::[] @ _3)
# 696 "grammar.ml"
               : 'cnf))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'cnf) in
    Obj.repr(
# 190 "grammar.mly"
                    (_2)
# 703 "grammar.ml"
               : 'cnf))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'literal) in
    Obj.repr(
# 194 "grammar.mly"
          (_1)
# 710 "grammar.ml"
               : 'clause))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'literal) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'clause) in
    Obj.repr(
# 195 "grammar.mly"
                    (_1 @ _3)
# 718 "grammar.ml"
               : 'clause))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'clause) in
    Obj.repr(
# 196 "grammar.mly"
                       (_2)
# 725 "grammar.ml"
               : 'clause))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'listterm) in
    Obj.repr(
# 200 "grammar.mly"
                              ((false, _1, _3) :: [])
# 733 "grammar.ml"
               : 'literal))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 201 "grammar.mly"
                     ((false, _1, []) :: [])
# 740 "grammar.ml"
               : 'literal))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'listterm) in
    Obj.repr(
# 202 "grammar.mly"
                                  ((true, _2, _4) :: [])
# 748 "grammar.ml"
               : 'literal))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 203 "grammar.mly"
                         ((true, _2, []) :: [])
# 755 "grammar.ml"
               : 'literal))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'literal) in
    Obj.repr(
# 204 "grammar.mly"
                        (_2)
# 762 "grammar.ml"
               : 'literal))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 208 "grammar.mly"
       ( _1 :: [] )
# 769 "grammar.ml"
               : 'listname))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'listname) in
    Obj.repr(
# 209 "grammar.mly"
                ( _1 :: _2)
# 777 "grammar.ml"
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
