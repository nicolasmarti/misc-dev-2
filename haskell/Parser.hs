{-# LANGUAGE ExistentialQuantification, FlexibleInstances, RankNTypes, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, UndecidableInstances, EmptyDataDecls, PatternGuards #-}

-- 

module Parser where

import Def

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Token
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Pos
import Text.ParserCombinators.Parsec.Error
import Text.ParserCombinators.Parsec.Expr

myTokenParser :: TokenParser ()
myTokenParser = makeTokenParser $ haskellStyle {
    reservedOpNames= ["::","..","=","\\","|","<-","->","@","~","=>"],
    reservedNames  = ["let","in","case","of","if","then","else",
                      "Type", "do","import",
                      "infix","infixl","infixr", "module",
                      "where", "V", 
                      "def"
                     ]
    }

-- the state for parsing :
data ParseState = ParseState {
    operators :: [(String, OpProp)]
    }

emptyPState :: ParseState
emptyPState = ParseState { operators = [] }


getSource :: Parser String
getSource = do { pos <- getPosition
               ; return $ sourceName pos
               }

getpos :: Parser (Int, Int)
getpos = do { pos <- getPosition
            ; let line = sourceLine pos
            ; let col = sourceColumn pos
            ; return (line, col)
            }


withPosition :: Parser a -> Parser (a, Position)
withPosition p = do {
    ; fname <- getSource
    ; (startline, startcol) <- getpos
    ; res <- p
    ; (endline, endcol) <- getpos
    ; return (res, Position (Just fname) ((startline, startcol), (endline, endcol)))
    }


termParser :: ParseState -> Parser Term
termParser st = parseTerm <?> "Expected a Term"
    where
        
        parseTypeAnnotation :: Parser TypeInfo
        parseTypeAnnotation = try (do {
                                       ; whiteSpace myTokenParser
                                       ; reservedOp myTokenParser "::"
                                       ; whiteSpace myTokenParser
                                       ; (ty, pos) <- withPosition parseTerm
                                       ; return $ Annotation ty pos
                                       }
                                  ) <|> (return NoType)

        withTypeInfo :: Parser a -> Parser (a, TypeInfo)
        withTypeInfo p = do {
            ; res <- p
            ; ty <- parseTypeAnnotation
            ; return (res, ty)
            }

        parseTerm :: Parser Term
        parseTerm = try parseOp
                    <|> parseTermLvl2

        parseTermLvl1 :: Parser Term
        parseTermLvl1 = try parseType
                        <|> try parseVar
                        <|> try parseAVar
                        <|> try parseLambda
                        <|> try parseForall
                        <|> try parseLet
                        <|> try parseCase
                        <|> try parseOp2
                        <|> try parseDo
                        <|> try (parens myTokenParser $ parseTerm)

        parseTermLvl2 :: Parser Term
        parseTermLvl2 = try parseApp
                        <|> parseTermLvl1

        parseType :: Parser Term
        parseType = do {
            ; whiteSpace myTokenParser
            ; (_, pos) <- withPosition $ reserved myTokenParser "Type"
            ; whiteSpace myTokenParser                          
            ; return (Type pos NoType)
            }

        parseVar :: Parser Term
        parseVar = do {
            ; whiteSpace myTokenParser
            ; ((s, pos), ty) <- withTypeInfo $ withPosition $ identifier myTokenParser
            ; whiteSpace myTokenParser                                
            ; return $ Var pos s Nothing ty
            }

        parseAVar :: Parser Term
        parseAVar = do {
            ; whiteSpace myTokenParser
            ; (((), pos), ty) <- withTypeInfo $ withPosition $ do {
                ; string "_"
                ; (notFollowedBy $ do { identifier myTokenParser; return ' '}) <?> "_ should not be followed by any characters"
                ; return ()
                }
            ; whiteSpace myTokenParser
            ; return $ AVar pos Nothing ty
            }

        parseQuantifier :: Parser Quantifier
        parseQuantifier = do {
            ; let oneVarQuantifier = do {                      
                      ; whiteSpace myTokenParser
                      ; res <- withPosition $ identifier myTokenParser
                      ; whiteSpace myTokenParser
                      ; return $ Quantifier ([res], NoType, Hidden)
                      }
            ; let severalVarQuantifier = do {
                      ; whiteSpace myTokenParser
                     ; vars <- many1 $ withPosition $ identifier myTokenParser
                     ; ty <- parseTypeAnnotation
                     ; whiteSpace myTokenParser
                     ; return (vars, ty)
                     }
            ; try oneVarQuantifier
              <|> try (do { (vars, ty) <- parens myTokenParser severalVarQuantifier
                          ; return $ Quantifier (vars, ty, Explicite)
                          }
                      )
              <|> try (do { (vars, ty) <- braces myTokenParser severalVarQuantifier
                          ; return $ Quantifier (vars, ty, Hidden)
                          }
                      )
              <|> try (do { (vars, ty) <- squares myTokenParser severalVarQuantifier
                          ; return $ Quantifier (vars, ty, Implicit)
                          }
                      )
            }

        parseLambda :: Parser Term
        parseLambda = do {
            ; whiteSpace myTokenParser
            ; (((quants, body), pos), ty) <- withTypeInfo $ withPosition $ do {
                ; reservedOp myTokenParser "\\"
                ; whiteSpace myTokenParser
                ; quants <- many1 parseQuantifier
                ; reservedOp myTokenParser "->"
                ; body <- parseTerm
                ; whiteSpace myTokenParser
                ; return (quants, body)
                }
            ; return $ Lambda quants body pos ty
            }

        parseForall :: Parser Term
        parseForall = do {
            ; whiteSpace myTokenParser
            ; (((quants, body), pos), ty) <- withTypeInfo $ withPosition $ do {
                ; reserved myTokenParser "V"
                ; whiteSpace myTokenParser
                ; quants <- many1 parseQuantifier
                ; reservedOp myTokenParser "->"
                ; body <- parseTerm
                ; return (quants, body)
                }
            ; return $ Forall quants body pos ty
            }

        parseLet :: Parser Term
        parseLet = do {
            ; whiteSpace myTokenParser
            ; (((var, def, body), pos), ty) <- withTypeInfo $ withPosition $ do {
                ; reserved myTokenParser "let"
                ; var <- identifier myTokenParser
                ; whiteSpace myTokenParser
                ; reservedOp myTokenParser "="
                ; def <- parseTerm
                ; reserved myTokenParser "in"
                ; body <- parseTerm
                ; return (var, def, body)
                }
            ; return $ Let [(var, def)] body pos ty
            }

        parseApp :: Parser Term
        parseApp = do {
            ; whiteSpace myTokenParser
            ; (((fct, args), pos), ty) <- withTypeInfo $ withPosition $ do {
                ; fct <- parseTermLvl1
                ; args <- many1 (try (do { arg <- parseTermLvl1
                                          ; return (Explicite, arg)
                                          }
                                      )
                                 <|> try (do { arg <- braces myTokenParser parseTerm
                                             ; return (Hidden, arg)
                                             }
                                         )
                                 <|> try (do { arg <- squares myTokenParser parseTerm
                                             ; return (Implicit, arg)
                                             }
                                         )
                                )
                ; return (fct, args)
                }
            ; return $ App fct args pos ty
            }


        parsePatternLvl1 :: Parser Pattern
        parsePatternLvl1 =  try (do {
                                     ; whiteSpace myTokenParser
                                     ; (((s, underp), pos), ty) <- withTypeInfo $ withPosition $ do {
                                         ; s <- identifier myTokenParser
                                         ; reservedOp myTokenParser "@"
                                         ; underp <- parens myTokenParser $ parsePattern
                                         ; return (s, underp)
                                         }
                                     ; return $ PAlias pos s underp ty
                                     })
                            <|> try (do {
                                   ; whiteSpace myTokenParser
                                   ; ((s, pos), ty) <- withTypeInfo $ withPosition $ identifier myTokenParser
                                   ; return $ PVar pos s ty
                                   })
                           <|> try (do {
                                        ; whiteSpace myTokenParser
                                        ; (((), pos), ty) <- withTypeInfo $ withPosition $ do {
                                            ; string "_"
                                            ; (notFollowedBy $ do { identifier myTokenParser; return ' '}) <?> "_ should not be followed by any characters"
                                            ; return ()
                                            }
                                        ; return $ PAVar pos ty
                                        })
                           <|> try (parens myTokenParser parsePattern)

        parsePatternApp :: Parser Pattern
        parsePatternApp = do {                
            ; whiteSpace myTokenParser
            ; (((fct, args), pos), ty) <- withTypeInfo $ withPosition $ do {
                ; fct <- parsePatternLvl1
                ; args <- many1 (try (do { arg <- parsePatternLvl1
                                          ; return (Explicite, arg)
                                          }
                                      )
                                 <|> try (do { arg <- braces myTokenParser parsePatternLvl1
                                             ; return (Hidden, arg)
                                             }
                                         )
                                 <|> try (do { arg <- squares myTokenParser parsePatternLvl1
                                             ; return (Implicit, arg)
                                             }
                                         )
                                )
                ; return (fct, args)
                }
            ; fct <- (case fct of
                         PVar pos name ty -> return name 
                         _ -> fail "wrong head of pattern"
                     )
            ; return $ PApp fct Nothing args pos ty
            }        

        parsePattern :: Parser Pattern
        parsePattern = try parsePatternApp
                       <|> try parsePatternLvl1


        parseGuard :: Parser Guard
        parseGuard = do {
            ; ((te, pos), ty) <- withTypeInfo $ withPosition $ parseTerm
            ; return (te, pos, ty)
            }

        parseCase :: Parser Term
        parseCase = do {
            ; whiteSpace myTokenParser
            ; (((te, cases), pos), ty) <- withTypeInfo $ withPosition $ do {
                ; reserved myTokenParser "case"
                ; te <- parseTerm
                ; whiteSpace myTokenParser
                ; reserved myTokenParser "of"
                ; cases <- many (do {
                                     -- ([(Pattern, [Guard], Maybe Term)], Term)
                                     ; pats <- many1 $ do { 
                                         -- (Pattern, [Guard], Maybe Term)
                                         ;reservedOp myTokenParser "|"
                                         ; whiteSpace myTokenParser 
                                         ; pat <- parsePattern
                                         ; whiteSpace myTokenParser   

                                         ; guards <- many $ do {
                                             ; whiteSpace myTokenParser 
                                             ; reserved myTokenParser "where"
                                             ; parseGuard
                                             }          

                                         ; return (pat, guards, Nothing)
                                         }

                                     ; whiteSpace myTokenParser                                      
                                     ; reservedOp myTokenParser "=>"                                               
                                     ; whiteSpace myTokenParser                                          
                                     ; def <- parseTerm
                                     ; return (pats, def)
                                     }
                                ) 
                ; return (te, cases)
                }
            ; return $ Case te cases pos ty
            }

        parsecOperatorTable :: OperatorTable Char () (Term, Position)
        parsecOperatorTable = 
            let base = replicate 250 [] in
            foldl (\ acc hd -> 
                   let (operator, str) = (
                           case hd of
                               (s, o@(OpInfix assoc str)) -> (Infix (do { (op, pos) <- withPosition $ reserved myTokenParser s
                                                                        ; return $ \ (t1, Position src1 (start1, end1)) 
                                                                                     (t2, Position src2 (start2, end2)) -> 
                                                                                            (App (Operator o s pos NoType Nothing Nothing) [(Explicite, t1), (Explicite, t2)] (Position src1 (start1, end2)) NoType, (Position src1 (start1, end2)))
                                                                        }
                                                              ) (case assoc of
                                                                     OpAssocNone -> AssocNone
                                                                     OpAssocLeft -> AssocLeft
                                                                     OpAssocRight -> AssocRight
                                                                     ), str
                                                             ) 
                               (s, o@(OpPrefix str)) -> (Prefix ( do {
                                                                      ; (op, pos@(Position srco (starto, endo))) <- withPosition $ reserved myTokenParser s
                                                                      ; return $ \ (t, Position src (start, end)) ->
                                                                                        (App (Operator o s pos NoType Nothing Nothing) [(Explicite, t)] (Position src (starto, end)) NoType, (Position src (starto, end)))
                                                                      }
                                                                ), str)                           
                           ) in
                   (take str acc) ++ [(acc!!str) ++ [operator]] ++ (drop (str + 1) acc)
                   ) base $ operators st


        parseOp :: Parser Term
        parseOp = do {
            ; (te, _) <- buildExpressionParser (reverse parsecOperatorTable) $ withPosition parseTermLvl2
            ; return te
            }

        parseOp2 :: Parser Term
        parseOp2 = do {
            ; (((s, o), ty), pos) <- foldl (<|>) (fail "this is the end ...") $ map (\ (s, o) -> try $ withPosition $ withTypeInfo $ do {
                                                                                         ; whiteSpace myTokenParser                                      
                                                                                         ; parens myTokenParser $ reservedOp myTokenParser s; return ()
                                                                                         ; whiteSpace myTokenParser                                                                                                                         
                                                                                         ; return (s, o)
                                                                                         }) $ operators st
            ; return $ Operator o s pos ty Nothing Nothing
            }

        parseDo :: Parser Term
        parseDo = do {
            ; ((stmts, pos), ty) <- withTypeInfo $ withPosition $ do {
                ; whiteSpace myTokenParser 
                ; reserved myTokenParser "do"
                ; whiteSpace myTokenParser               
                ; reservedOp myTokenParser "{"  
                ; whiteSpace myTokenParser               
                ; stmts <- many1 (try (do { 
                                           ; (((var, te), ty), pos) <- withPosition $ withTypeInfo $ do {whiteSpace myTokenParser
                                                                                                        ; reservedOp myTokenParser ";"  
                                                                                                        ; whiteSpace myTokenParser  
                                                                                                        ; reserved myTokenParser "let"
                                                                                                        ; whiteSpace myTokenParser               
                                                                                                        ; id <- identifier myTokenParser
                                                                                                        ; reservedOp myTokenParser "="  
                                                                                                        ; whiteSpace myTokenParser  
                                                                                                        ; te <- parseTerm
                                                                                                        ; return (id, te)
                                                                                                        }
                                           ; return $ DoLet var pos ty te
                                           }
                                      )
                                  <|> try (do { 
                                               ; (((var, te), ty), pos) <- withPosition $ withTypeInfo $ do {whiteSpace myTokenParser
                                                                                                            ; reservedOp myTokenParser ";"  
                                                                                                            ; whiteSpace myTokenParser  
                                                                                                            ; id <- identifier myTokenParser
                                                                                                            ; reservedOp myTokenParser "<-"  
                                                                                                            ; whiteSpace myTokenParser  
                                                                                                            ; te <- parseTerm
                                                                                                            ; return (id, te)
                                                                                                            }
                                               ; return $ DoBind var pos ty te
                                               }
                                      )
                                  <|> try (do { 
                                               ; ((te, ty), pos) <- withPosition $ withTypeInfo $ do {whiteSpace myTokenParser
                                                                                                            ; reservedOp myTokenParser ";"  
                                                                                                            ; whiteSpace myTokenParser  
                                                                                                            ; parseTerm
                                                                                                            }
                                               ; return $ DoVal te pos ty
                                               }
                                      )
                                 )                                  
                ; whiteSpace myTokenParser               
                ; reservedOp myTokenParser "}"  
                ; return stmts
                }
            ; return $ DoNotation stmts pos ty
            }

definitionParser :: ParseState -> Parser Definition
definitionParser st = definitionParser' <?> "Expected a Definition"
    where
        definitionParser' :: Parser Definition
        definitionParser' = try parseSig
        
        
        parseSig :: Parser Definition
        parseSig = do {
            ; whiteSpace myTokenParser            
            ; reserved myTokenParser "def"
            ; whiteSpace myTokenParser                          
            ; ((id, ty), pos) <- withPosition $ do { 
                ; id <- identifier myTokenParser
                ; whiteSpace myTokenParser            
                ; reservedOp myTokenParser "::"
                ; whiteSpace myTokenParser            
                ; (ty, pos) <- withPosition $ termParser st
                ; return (id, ty)
                }
            ; return $ DefSig id pos ty              
            }
