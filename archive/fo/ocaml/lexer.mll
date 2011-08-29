{
  open Grammar 

}

let name = ['A'-'Z' 'a'-'z' '0'-'9']
    rule token = parse
      | [' ' '\t' '\n' '\r']+ { token lexbuf }
          
      | "true"      { TRUE }
      | "false"     { FALSE }    

      | '~'         { NEG }      
      | "/\\"        { AND }
      | "&"        { AND2 }
      | "\\/"        { OR }
      | "->"        { IMPL }
      | "==>"        { IMPL2 }
      | "-->"        { IMPL3 }

      | "<->"        { IFF }
      | "<=>"        { IFF2 }

      | 'V'		{ FORALL }
      | "forall"	{ FORALL2 }
      | "ALL"	        { FORALL3 }

      | 'E'		{ EXISTS }        
      | "exists"	{ EXISTS2 }        
      | "EXISTS"        { EXISTS3 }

      | "SPASS "	{ SPASS }        

      | name+ as word { NAME word }

      | '('		{ LPAREN }
      | ')'		{ RPAREN }

      | '['		{ LBRACK }
      | ']'		{ RBRACK }

      | ','		{ COMMA }
      | '.'		{ DOT }

      | '|'             { BAR }

      | '<'             { LT }

      | ';'             { SEMICOLON }

      | eof		{ EOF }
