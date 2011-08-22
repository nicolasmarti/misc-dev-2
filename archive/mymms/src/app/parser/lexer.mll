{

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

  open Lexing;;
  open Parser;;

}

let digit = ['0'-'9']
let namebasic = ['A'-'Z' 'a'-'z' '0'-'9']+ ['A'-'Z' 'a'-'z' '0'-'9' '_']*
let mstring = '"' ['A'-'Z' 'a'-'z' '0'-'9' ' ' ',' '!' '.']* '"'
let name = (namebasic '.')* namebasic
    
  rule token = parse
    | [' ' '\t' '\r']+ { token lexbuf }
    | '\n' { new_line lexbuf; token lexbuf }

    (* Symbols *)
    | "==>" { MATCHDESTRUCTOR }
    | "_" { UNDERSCORE }
    | '(' { LPAREN }
    | ')' { RPAREN }
    | '[' { LBRACK }
    | ']' { RBRACK }
    | '{' { LACCOL }
    | '}' { RACCOL }       
    | ',' { COMMA }
    | ';' { SCOMMA }
    | '|' { PAR}
    | ':' { COLON }
    | '.' { DOT }
    | "=" { EQ }
    | "->" { IMPL }
    | "<-" { ASSIGN }
    | "@" { AROBAS }
    | '"' { GUIL }
    | "'" { APPO }
    | "do" { DO }

    (* Terms *)
    | "\\" { LAMBDA }
(*
    | '!' { PHI }
    | 'I' { IND }
*)
    | 'V' { FORALL }
    | "match" { MATCH }
    | "returns" { RETURN }
    | "with" { WITH }
    | "Type" { TYPE }
(*
    | "cons" { CONS }
    | "of" { OF }
*)
    | "let" { LET }
    | "if" { IF }
    | "then" { THEN }
    | "else" { ELSE }

    (* Proof *)
    | "Lemma" { LEMMA }
    | "Qed" { QED }
    | "Defined" { DEFINED }
    | "Drop" { DROP }

    (* Tactics *)
    | "equiv" { EQUIV }
    | "intro" { INTRO } 
    | "intros" { INTROS } 
    | "generalize" { GENERALIZE } 
    | "as" { AS } 
    | "apply" { APPLY } 
    | "exact" { EXACT } 
    | "simpl" { SIMPL } 
    | "in" { IN } 
    | "factorize" { FACTORIZE } 
    | "destruct" { DESTRUCT } 
    | "unfold" { UNFOLD } 
    | "idtac" { IDTAC }
    | "Fail" { FAIL }
    | "repeat" { REPEAT }
    | "do" { DO }
    | "try" { TRY }
    | "oracle" { ORACLE }

    (* Info *)
    | "Show" { SHOW }
    | "Show Definitions" { SHOWDEF }
    | "Show Coercions" { SHOWCOERCION }
    | "Show Goal" { SHOWGOAL }
    | "Show Implicite" { SHOWIMPLICITE }
    | "Show Overload" { SHOWOVERLOAD }
    | "Show Tactics" { SHOWTACTICS }
    | "Simpl" { SIMPL }
    | "Interp " { INTERP }
    | "VMCompute" { VMCOMPUTE }
    | "Compute" { COMPUTE }
    | "Check" { TYPECHECK }

    (* Control *)
    | "Quit" { QUIT }
    | "Undo" { UNDO }
    | "Require" { REQUIRE }
    | "Load" { LOAD }
    | "Open" { OPEN }
    | "Close" { CLOSE }
    | "Variable" { VARIABLE }

    (* Definitions *)
    | "Inductive" { INDUCTIVE }
    | "Recursive" { RECURSIVE }
    | "Definition" { DEFINITION }
    | "Coercion" { COERCION }
    | "Overload" { OVERLOAD }
    | "Implicite" { IMPLICITE }
    | "Mutual" { MUTUAL }
    | "let" { LET }

	

    (* Overloaded functions *)
    | "+" { PLUS }
    | "-" { MINUS }
    | "*" { MULTIPLY }
    | "/" { DIVIDE }
    | "/\\" { AND }
    | "\\/" { OR }
    | "~" { NEG }
    | "<" { LT }
    | ">" { GT }

    (* Boolean *)
    | "!" { BNEG }
    | "&&" { BAND }
    | "||" { BOR }

    (* Numbers *)
    | digit+ as num { NUM num }

    | "." digit+
    | digit+ "." digit+ as num
	{ FLOAT (float_of_string num) }

    (* general *)
    | name as word { NAME word }
        
    | mstring as word { MSTRING word }

    | eof { EOF }

