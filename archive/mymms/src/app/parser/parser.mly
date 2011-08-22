%{

  (*
    This file is part of Mymms.

    Mymms is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Mymms is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with Mymms.  If not, see <http://www.gnu.org/licenses/>.

    Copyright (C) 2008 Nicolas Marti
  *)

  open Printf;;
  open Lexing;;
  open List;;
  open String;;

  open Varmap;;
  open Def;;
  open Term;;

  open Tactic;;
  open Command;;

  (* standard lib *)
  open MQ;;
  open MZ;;
  open MN;;
  open Mfloat;;
  open Mstring;;

  open Num;;
  open Big_int;;

  open Printer;;

  open State;;
  open Unfold;;
  open Termeq;;
  open Definition;;

  open Output

  let parse_error s =
    print_error "Parse error";
    print_error s;
  ;;

%}

/*********/
/* Terms */
/*********/ 


/* quantifier */
/* IND PHI */
%token LAMBDA  FORALL
  
/* term */
/* CONS OF */
%token MATCH RETURN WITH TYPE IMPL APP LET IF THEN ELSE DO ASSIGN



  /************/
  /*  General */
  /************/
%token NEWLINE EOF

  /* The indentifiers variables */
%token <string> NAME MSTRING

  /* Integer */
%token <string> NUM

%token <float> FLOAT

  /* parenthese */
%token LPAREN RPAREN LBRACK RBRACK LACCOL RACCOL

  /* ponctuation */
%token PAR SCOMMA COMMA DOT COLON TURNSTIL EQ MATCHDESTRUCTOR

  /* Special Characters */
%token UNDERSCORE AROBAS GUIL APPO
  



  /***********/
  /* Tactics */
  /***********/

  /* tactics */
%token EQUIV INTRO INTROS GENERALIZE AS APPLY EXACT SIMPL IN FACTORIZE DESTRUCT DEFINED UNFOLD FAIL IDTAC REPEAT DO TRY ORACLE

  
  /***********************/
  /* Overloaded functions */
  /***********************/
%token PLUS MINUS MULTIPLY DIVIDE
%token AND OR NEG 
%token EQ LT GT

  /********************/
  /* Standard Library */
  /********************/

  /* Boolean */
%token BNEG BAND BOR TRUE FALSE

  /***************/
  /* Definitions */
  /***************/

%token MUTUAL INDUCTIVE RECURSIVE DEFINITION LET

  /************/
  /* Commands */
  /************/

%token COERCION OVERLOAD IMPLICITE 

  /*********/
  /* Proof */
  /*********/

%token LEMMA QED DEFINED DROP 

  /********/
  /* Info */
  /********/

%token SHOWDEF SHOWCOERCION SHOWGOAL SIMPL INTERP VMCOMPUTE COMPUTE TYPECHECK SHOWIMPLICITE SHOWOVERLOAD SHOW SHOWTACTICS

  /***********/
  /* Control */
  /***********/

%token UNDO QUIT REQUIRE OPEN CLOSE LOAD VARIABLE

  /********************************/
  /* Associativity and precedence */
  /********************************/


%right IMPL
%nonassoc PAR
%nonassoc SCOMMA
%left PLUS MINUS OR BOR
%left MULTIPLY DIVIDE AND BAND
%left NEG BNEG
%nonassoc LT GT

  /****************/
  /* Entry points */
  /****************/

%start term tactic definition listdefinition typeckinfo proof info control input inputs
%type <Def.term> term
%type <Tactic.tactics> tactic
%type <Command.definition> definition
%type <Command.definition list> listdefinition
%type <Command.typeckinfo> typeckinfo
%type <Command.proof> proof
%type <Command.info> info
%type <Command.control> control
%type <unit> input
%type <unit> inputs
  
%% /* Grammar rules and actions follow */

  /*********/
  /* Input */
  /*********/

  inputs:

| input inputs { $1; 
		 if (List.length output_st.normal > 0) then printf "%s\n\n" (String.concat "" (List.rev output_st.normal)) else ();
		 if (List.length output_st.error > 0) then printf "%s\n\n" (String.concat "" (List.rev output_st.error)) else ();
		 if (List.length output_st.debug > 0) then printf "%s\n" (String.concat "" (List.rev output_st.debug)) else ();
		 flush stdout;
		 init_output ();
		 $2 
	       }
| EOF { () }

      input:
| control { manageCommand (CmdControl $1) }
| definition { manageCommand (CmdDefinition $1) }
| typeckinfo { manageCommand (CmdTypeckinfo $1) }
| proof { manageCommand (CmdProof $1) }
| info { manageCommand (CmdInfo $1) }

  ;

  /***********/
  /* Control */
  /***********/
    
    control:
| QUIT DOT { Quit }
| UNDO DOT { Undo }
| REQUIRE NAME DOT { Require $2 }      
| LOAD NAME DOT { Load $2 }      
| OPEN NAME DOT { Open $2 }
| CLOSE DOT { Close }
| VARIABLE NAME COLON term DOT { Variable ($2, $4) }
  ;
  
  /********/
  /* Info */
  /********/
    
    info:
| SHOWDEF DOT { ShowDef }
| SHOWCOERCION DOT { ShowCoercion }
| SHOWIMPLICITE DOT { ShowImplicite }
| SHOWOVERLOAD DOT { ShowOverload }
| SHOWGOAL DOT { ShowGoal }
| SIMPL term DOT { Simpl ($2, None) }
| SIMPL term COLON term DOT { Simpl ($2, Some $4) }
| INTERP term DOT { Interp ($2, None) }
| INTERP term COLON term DOT { Interp ($2, Some $4) }
| VMCOMPUTE term DOT { VMCompute ($2, None) }
| VMCOMPUTE term COLON term DOT { VMCompute ($2, Some $4) }
| COMPUTE term DOT { Compute ($2, None) }
| COMPUTE term COLON term DOT { Compute ($2, Some $4) }
| TYPECHECK term DOT { Typecheck ($2, None) }
| TYPECHECK term COLON term DOT { Typecheck ($2, Some $4) }
| SHOW term DOT { Show $2 }
| SHOWTACTICS DOT { ShowTactics }
  ;

  /*********/
  /* Proof */
  /*********/

    proof:

| LEMMA NAME COLON term DOT { Lemma ($2, $4) }
| QED DOT { Qed }
| DEFINED DOT { Defined }
| DROP DOT { Drop }
| tactic DOT { Tactic $1 }

  ;

  /**************/
  /* Typeckinfo */
  /**************/

    typeckinfo:
| COERCION term DOT {

    Coercion ($2)

  }

| COERCION term AS term DOT {

    CoercionAs ($2, $4)

  }

| OVERLOAD NAME WITH term LBRACK NUM RBRACK DOT {

    Overload ($2, $4, (int_of_string $6))

  }
| IMPLICITE NAME LBRACK NUM RBRACK DOT {

    Implicite ($2, (int_of_string $4))

  }
  ;

  /***************/
  /* Definitions */
  /***************/


    listdefinition:

| definition  { $1 :: [] }
| definition listdefinition { $1 :: $2 }
| EOF { [] }

      definition:

| INDUCTIVE inductivedef DOT { Inductive $2 }

| INDUCTIVE mutualinductivedef DOT { MutualInductive $2 }

| DEFINITION definitiondef DOT { Definition $2 }

| RECURSIVE recursivedef DOT { Recursive $2 }   

| RECURSIVE mutualrecursivedef DOT { MutualRecursive $2 }

  ;

  recursivedef:

| NAME listargs LBRACK listnum RBRACK COLON term COLON EQ term {

    ($1, $2, Some $4, $7, $10)

  }

| NAME listargs LBRACK listnum RBRACK COLON EQ term {

    ($1, $2, Some $4, Avar, $8)

  }

| NAME listargs COLON term COLON EQ term {

    ($1, $2, None, $4, $7)

  }

| NAME listargs COLON EQ term {

    ($1, $2, None, Avar, $5)

  }

  ;

  mutualrecursivedef:
| recursivedef { $1::[] }
| recursivedef WITH mutualrecursivedef { $1::$3 }
  ;

  
  definitiondef:
| NAME listargs COLON term COLON EQ term {

    ($1, (largs_lambdas $7 $2), Some (largs_foralls $4 $2))

  }

| NAME listargs COLON EQ term {

    ($1, (largs_lambdas $5 $2), None)

  }

  ;


  inductivedef:

| NAME listargs COLON term COLON EQ constructors {

    ($1, $2, $4, $7)

  }

| NAME listargs COLON EQ constructors {

    ($1, $2, Avar, $5)

  }

  ;

  mutualinductivedef:
| inductivedef { $1::[] }
| inductivedef WITH mutualinductivedef { $1::$3 }
  ;



  constructors:
| constructors constructors { $1 @ $2 }
| PAR NAME COLON term { ($2, $4)::[] }
| { [] }
  ;


  /*********/
  /* Terms */
  /*********/

 term:

| terma {

    $1
      
  }

| terma suiteterm {
    let te1 = $1 in
    let te2 = $2 in
      App (te1,te2)
  }

| term IMPL term {
    
    let te = $1 in
    let te2 = $3 in
    let x = "Hyp" in
      Forall (x, te, te2)

}

/* Symbols for some type class */
| term EQ EQ term { App(Cste "equal", $1::$4::[])}
| term PLUS term { App(Cste "plus", $1::$3::[])}
| term MINUS term { App(Cste "minus", $1::$3::[])}
| term MULTIPLY term { App(Cste "mult", $1::$3::[])}
| term DIVIDE term { App(Cste "divide", $1::$3::[])}
| term GT EQ term { App(Cste "gte", $1::$4::[])}
| term GT term { App(Cste "gt", $1::$3::[])}
| term LT EQ term { App(Cste "lte", $1::$4::[])}
| term LT term { App(Cste "lt", $1::$3::[])}


/* Logic */
| term OR term { App(Cste "StdLib.Logic.or", $1::$3::[])}
| term AND term { App(Cste "StdLib.Logic.and", $1::$3::[])}
| NEG term { App(Cste "StdLib.Logic.not", $2::[])}

/* Boolean */
| BNEG term { App (Cste "StdLib.Bool.bneg", $2::[]) }
| term BAND term { App (Cste "StdLib.Bool.band", $1::$3::[]) }
| term BOR term { App (Cste "StdLib.Bool.bor", $1::$3::[]) }
 
;

  terma:

| UNDERSCORE {

    Avar

  }

| NAME { 

    Var $1

  }

| AROBAS NAME {

    Cste $2

  }

| LET NAME COLON EQ term IN term {

    Let ($2, $5, $7)

  }

| LET term COLON EQ term IN term {

    AdvMatch ($5, ($2, $7)::[], None)

  }

| LAMBDA listargs DOT term {

      largs_lambdas $4 $2

  }

| LAMBDA listargs IMPL term {

      largs_lambdas $4 $2

  }

| FORALL listargs DOT term {

    largs_foralls $4 $2

  }

| MATCH term WITH destructors {
    Match ($2, $4, None, None)
  }

| MATCH term RETURN term WITH destructors {
    Match ($2, $6, Some $4, None)
  }


| MATCH term WITH advdestructors {
    AdvMatch ($2, $4, None)
  }

| MATCH term RETURN term WITH advdestructors {
    AdvMatch ($2, $6, Some ($4))
  }

/*
| CONS NUM OF term {
    Cons ((int_of_string $2), $4)
  }
*/

| TYPE { Type }

| LPAREN term RPAREN { $2 }

/* Could change if the bool are to be mymms terms */

| IF term THEN term ELSE term {

    Match ($2, ($4 :: $6 :: []), None, None)

  }

/* do notation */
| DO LPAREN NAME RPAREN LACCOL donotation2 RACCOL { $6 (Var $3) }

| DO LACCOL donotation RACCOL { $3 }

/* Only for testing */

/*
| PHI LPAREN NAME COMMA LPAREN context RPAREN COMMA term COMMA LBRACK listnum RBRACK RPAREN DOT term {
    Phi ($3, $6, $9, $12, $16)
  }

| IND LPAREN NAME COMMA LPAREN context RPAREN COMMA term RPAREN DOT listterm {
    Ind ($3, $6, $9, $12)
  }
*/

/* Num */
| NUM { create_mNTerm (big_int_of_string $1) }

| LPAREN MINUS NUM RPAREN { create_mZTerm (big_int_of_string (concat " " ("-"::$3::[]))) }

| FLOAT { create_floatTerm $1 }

/* String */
| MSTRING { create_stringTerm (String.sub $1 1 (String.length $1 - 2 )) }

| APPO NAME APPO { if (length $2 > 1) then create_stringTerm $2
		   else create_charTerm $2.[0]
		 }

;

  donotation:

| NAME ASSIGN term SCOMMA donotation { App (Var "StdLib.Monad.bind", $3 :: (Lambda ($1, Avar, $5)) :: []) }

| LET NAME COLON EQ term SCOMMA donotation { Let ($2, $5, $7) }

| LET term COLON EQ term SCOMMA donotation {

    AdvMatch ($5, ($2, $7)::[], None)

  }

| term SCOMMA donotation { App (Var "StdLib.Monad.bind", $1 :: (Lambda ("@_@", Avar, $3)) :: []) }

| term { $1 }



  donotation2:

| NAME ASSIGN term SCOMMA donotation2 { fun x -> App (Cste "StdLib.Monad.bind", x :: Avar :: Avar :: Avar :: $3 :: (Lambda ($1, Avar, $5 x)) :: []) }

| LET NAME COLON EQ term SCOMMA donotation2 { fun x -> Let ($2, $5, $7 x) }

| LET term COLON EQ term SCOMMA donotation2 {

    fun x -> AdvMatch ($5, ($2, $7 x)::[], None)

  }

| term SCOMMA donotation2 { fun x -> App (Var "StdLib.Monad.bind", $1 :: (Lambda ("@_@", Avar, $3 x)) :: []) }

| term { fun x -> $1 }




  listterm:
| term { $1 :: [] }
| listterm COMMA listterm { $1 @ $3 }
| LPAREN listterm RPAREN { $2 }
| LPAREN RPAREN { [] }
  ;


  suiteterm:
| terma { $1::[] }
| terma suiteterm { $1 :: $2 }
  ;

  listname:
| NAME { $1::[] }
| NAME listname { $1 :: $2 }

  args:      
| LPAREN NAME COLON term RPAREN { ($2,$4)::[] }
| NAME { ($1, Avar)::[] }
| LPAREN listname COLON term RPAREN { 
    
    List.fold_left (
      
      fun acc hd ->
	acc @ (hd, $4)::[]

    ) [] $2

  };

  context:
| args { $1 }
| args COMMA context { $1 @ $3 }
| { [] } 
  ;
  
  listargs:
    
| args { $1 }
| args listargs { $1 @ $2}
| { [] }
  ;

  destructors:
| destructors destructors {$1 @ $2 }
| PAR term { $2::[] }
| { [] } 
  ;

  advdestructors:
| advdestructors advdestructors {$1 @ $2 }
| PAR term MATCHDESTRUCTOR term  { ($2, $4)::[] }
| { [] } 
  ;

  listnum:
| NUM { (int_of_string $1)::[] }
| listnum COMMA listnum {$1 @ $3}
| { [] }
  ;

  /***********/
  /* Tactics */
  /***********/

    tactic:

| LPAREN tactic RPAREN {

    $2

  }

| tactic SCOMMA tactic {

    TacticSeq ($1, $3)

  }

| DO NUM tactic { Dotactic ((int_of_string $2), $3) }

| TRY tactic { Trytactic $2 }

| LBRACK listtactic RBRACK { Partactic $2 }

| LPAREN listtactic2 RPAREN { Ortactic $2 }

| REPEAT tactic { Repeat $2 }

| EQUIV term {

    Equiv $2
      
  }


| IDTAC { Idtac }

| FAIL { Fail }

| INTRO {

    Intro

  }

| INTRO NAME {

    IntroAs $2

  }

| INTROS {

    Repeat Intro

  }

| EXACT term {

    Exact $2

  }

| APPLY term {
    
    Apply $2

  }

| GENERALIZE term AS NAME {

    Generalize ($2, $4)
      
  }

| SIMPL {
    
    Tactic.Simpl
  }

| SIMPL IN NAME {

    SimplIn $3
      
  }

| FACTORIZE suiteterm {
    
    Factorize $2

  }

| DESTRUCT term {

    Destruct $2
      
  }

| ORACLE NAME { 
    
    Oracle $2 
  
  }
    
  ;

  listtactic:
    
| tactic { $1::[] }

| listtactic PAR listtactic { $1 @ $3 }

  ;

  listtactic2:
    
| tactic { $1::[] }

| listtactic2 PAR PAR listtactic2 { $1 @ $4 }

  ;

