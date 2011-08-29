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
      | "\\/"        { OR }
      | "->"        { IMPL }
      | "==>"        { IMPL2 }

      | "<->"        { IFF }
      | "<=>"        { IFF2 }

      | 'V'		{ FORALL }
      | "forall"	{ FORALL2 }

      | 'E'		{ EXISTS }        
      | "exists"	{ EXISTS2 }        

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

      | eof		{ EOF }
