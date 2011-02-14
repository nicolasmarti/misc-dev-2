{-# LANGUAGE ExistentialQuantification, FlexibleInstances, RankNTypes, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, UndecidableInstances, EmptyDataDecls #-}

-- this is a little language to be compile in VM

module Trep (

    Position (..), Term(..),

    main

    ) where


import VM

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Token
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Pos
import Text.ParserCombinators.Parsec.Error
import Text.ParserCombinators.Parsec.Expr

import Text.PrettyPrint.HughesPJ hiding (char, parens, braces)
import Text.PrettyPrint.HughesPJClass hiding (char, parens, braces)

import qualified Text.PrettyPrint.HughesPJ as Pretty(char, parens, braces, brackets)
import qualified Text.PrettyPrint.HughesPJClass as Pretty(char, parens, braces, brackets)

import Data.Bits


-- *******************************************************************
-- AST for Trep
-- *******************************************************************

data Position = NoPosition
              | Position (Maybe String) {- file name-} ((Int, Int), (Int, Int))
              deriving (Eq, Show, Ord, Read)

data TypeInfo = NoType
              | Annotation Term Position
              | Infered Term
              deriving (Eq, Show, Ord, Read)

data Term = Type Position
          | Var Position Name (Maybe Int) TypeInfo

          | AVar Position (Maybe Term) TypeInfo

          | Cste Position Name TypeInfo (Maybe Term)

          | Lambda [Quantifier] Term Position TypeInfo
          | Forall [Quantifier] Term Position TypeInfo

          | Ind Name [Quantifier] Term [(Name, Term)] Position TypeInfo
          | Constr Int Term Position TypeInfo

          | Let [(Name, Term)] Term Position TypeInfo

          | App Term [(Nature, Term)] Position TypeInfo

          | Case Term [([(Pattern, [Guard])], Term)] Position TypeInfo

          | DoNotation [DoStmt] Position TypeInfo

          | Operator OpProp String Position TypeInfo Term
          deriving (Eq, Show, Ord, Read)

data OpProp = OpProp OpAssoc BindStrentgh
            deriving (Eq, Show, Ord, Read)

type BindStrentgh = Int

data OpAssoc = OpAssocLeft
             | OpAssocRight
             deriving (Eq, Show, Ord, Read)

data Quantifier = Quantifier ([(Name, Position)], TypeInfo, Nature)
                deriving (Eq, Show, Ord, Read)

data Pattern = PAVar Position TypeInfo
             | PCste Position Name TypeInfo
             | PVar Position Name TypeInfo
             | PApp Name [(Nature, Pattern)] Position TypeInfo
             | PAlias Position Name Pattern TypeInfo
             deriving (Eq, Show, Ord, Read)

type Guard = (Term, Position, TypeInfo)

data DoStmt = DoLet Name Position TypeInfo Term
            | DoBind Name Position TypeInfo Term
            | DoVal Term Position TypeInfo
            deriving (Eq, Show, Ord, Read)

type Name = String

data Nature = Implicite
            | Explicite
            | Oracled
            deriving (Eq, Show, Ord, Read)

-- *******************************************************************
-- Parser / Pretty printer
-- *******************************************************************

myTokenParser :: TokenParser ()
myTokenParser = makeTokenParser $ haskellStyle {
    reservedOpNames= ["::","..","=","\\","|","<-","->","@","~","=>"],
    reservedNames  = ["let","in","case","of","if","then","else",
                      "Type", "do","import",
                      "infix","infixl","infixr", "module",
                      "where", "V"]
    }

-- the state for parsing :
data ParseState = ParseState {
    operators :: OperatorTable Char () Term
    }

dummyPState :: ParseState
dummyPState = ParseState { operators = [] }

trepParser :: ParseState -> Parser (Term, TypeInfo)
trepParser st = (withTypeInfo parseTerm) <?> "Expected a Term"
    where
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
        parseTerm = try parseApp
                    <|> parseTermLvl1

        parseTermLvl1 :: Parser Term
        parseTermLvl1 = try parseType
                        <|> try parseVar
                        <|> try parseAVar
                        <|> try parseLambda
                        <|> try parseForall
                        <|> try parseLet
                        <|> try parseCase
                        <|> try (parens myTokenParser $ parseTerm)

        parseType :: Parser Term
        parseType = do {
            ; whiteSpace myTokenParser
            ; (_, pos) <- withPosition $ reserved myTokenParser "Type"
            ; return (Type pos)
            }

        parseVar :: Parser Term
        parseVar = do {
            ; whiteSpace myTokenParser
            ; ((s, pos), ty) <- withTypeInfo $ withPosition $ identifier myTokenParser
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
            ; return $ AVar pos Nothing ty
            }

        parseQuantifier :: Parser Quantifier
        parseQuantifier = do {
            ; let oneVarQuantifier = do {
                      ; res <- withPosition $ identifier myTokenParser
                      ; return $ Quantifier ([res], NoType, Implicite)
                      }
            ; let severalVarQuantifier = do {
                     ; vars <- many1 $ withPosition $ identifier myTokenParser
                     ; ty <- parseTypeAnnotation
                     ; return (vars, ty)
                     }
            ; try oneVarQuantifier
              <|> try (do { (vars, ty) <- parens myTokenParser severalVarQuantifier
                          ; return $ Quantifier (vars, ty, Explicite)
                          }
                      )
              <|> try (do { (vars, ty) <- braces myTokenParser severalVarQuantifier
                          ; return $ Quantifier (vars, ty, Implicite)
                          }
                      )
              <|> try (do { (vars, ty) <- squares myTokenParser severalVarQuantifier
                          ; return $ Quantifier (vars, ty, Oracled)
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
                                 <|> try (do { arg <- braces myTokenParser parseTermLvl1
                                             ; return (Implicite, arg)
                                             }
                                         )
                                 <|> try (do { arg <- squares myTokenParser parseTermLvl1
                                             ; return (Oracled, arg)
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
                                             ; return (Implicite, arg)
                                             }
                                         )
                                 <|> try (do { arg <- squares myTokenParser parsePatternLvl1
                                             ; return (Oracled, arg)
                                             }
                                         )
                                )
                ; return (fct, args)
                }
            ; fct <- (case fct of
                         PVar pos name ty -> return name 
                         PCste pos name ty -> return name                    
                         _ -> fail "wrong head of pattern"
                     )
            ; return $ PApp fct args pos ty
            }        
        
        parsePattern :: Parser Pattern
        parsePattern = try parsePatternApp
                       <|> try parsePatternLvl1
        

        parseCase :: Parser Term
        parseCase = do {
            ; whiteSpace myTokenParser
            ; (((te, cases), pos), ty) <- withTypeInfo $ withPosition $ do {
                ; reserved myTokenParser "case"
                ; te <- parseTerm
                ; whiteSpace myTokenParser
                ; reserved myTokenParser "of"
                ; cases <- many (do {
                                     ; reservedOp myTokenParser "|"
                                     ; whiteSpace myTokenParser 
                                     ; pat <- parsePattern
                                     ; whiteSpace myTokenParser                                                 
                                     ; reservedOp myTokenParser "=>"
                                     ; whiteSpace myTokenParser                                          
                                     ; def <- parseTerm
                                     ; return ([(pat, [])], def)
                                     }) 
                ; return (te, cases)
                }
            ; return $ Case te cases pos ty
            }



-- precision is an Int
-- using bits ...
-- 1: show types
-- 2: show position

typeShowLvl :: Int -> Bool
typeShowLvl = flip testBit 0

posShowLvl :: Int -> Bool
posShowLvl = flip testBit 1

instance Pretty Position where
    pPrintPrec lvl prec NoPosition = empty
    pPrintPrec lvl prec (Position src ((startline, startcol), (endline, endcol))) = (maybe empty (\ s -> text "@" <> text s <> text ":") src) <> int startline <> text ":" <> int startcol <> text "-" <> int endline <> text ":" <> int endcol

instance Pretty TypeInfo where
    pPrintPrec lvl prec NoType = empty
    pPrintPrec lvl prec (Annotation te pos) = text "::" <+> pPrintPrec lvl prec te
    pPrintPrec lvl prec (Infered te) = text ":?:" <+> pPrintPrec lvl prec te

instance Pretty Quantifier where
    pPrintPrec lvl prec (Quantifier ([(var, pos)], NoType, Implicite)) = text var
    pPrintPrec lvl prec (Quantifier (vars, ty, Explicite)) = Pretty.parens $ foldl (<+>) empty (map (text . fst) vars) <+> (pPrintPrec lvl prec ty)
    pPrintPrec lvl prec (Quantifier (vars, ty, Implicite)) = Pretty.braces $ foldl (<+>) empty (map (text . fst) vars) <+> (pPrintPrec lvl prec ty)
    pPrintPrec lvl prec (Quantifier (vars, ty, Oracled)) = Pretty.brackets $ foldl (<+>) empty (map (text . fst) vars) <+> (pPrintPrec lvl prec ty)


instance Pretty Pattern where
    pPrintPrec lvl prec (PAVar _ _) = text "_"
    pPrintPrec lvl prec (PCste _ name _) = text name
    pPrintPrec lvl prec (PVar _ name _) = text name
    pPrintPrec lvl prec (PApp fct args pos ty) = text fct  
                                                 <+> foldl (\ acc hd -> acc <+> ((case fst hd of
                                                                                      Explicite -> id
                                                                                      Implicite -> Pretty.braces
                                                                                      Oracled -> Pretty.brackets
                                                                                 ) $ pPrintPrec lvl prec $ snd hd
                                                                                )
                                                           ) empty args
    pPrintPrec lvl prec (PAlias _ name underp _) = text name <> text "@" <> Pretty.parens (pPrintPrec lvl prec underp)
    
instance Pretty Term where
    pPrintPrec lvl@(PrettyLevel i) prec (Type pos) = 
        text "Type" <+> (if posShowLvl i then pPrintPrec lvl prec pos else empty)
        
    pPrintPrec lvl@(PrettyLevel i) prec (Var pos name debruijn ty) = 
        text name <+> (if typeShowLvl i then pPrintPrec lvl prec ty else empty) <> (if posShowLvl i then pPrintPrec lvl prec pos else empty)
        
    pPrintPrec lvl@(PrettyLevel i) prec (AVar pos _ ty) = 
        text "_" <+> (if typeShowLvl i then pPrintPrec lvl prec ty else empty) <+> (if posShowLvl i then pPrintPrec lvl prec pos else empty)
        
    pPrintPrec lvl@(PrettyLevel i) prec (Lambda quants body pos ty) = 
        fsep [
            text "\\" <+> foldl (\ acc hd -> acc <+> pPrintPrec lvl prec hd) empty quants <+> text "->", 
            nest 2 $ pPrintPrec lvl prec body, 
            (if typeShowLvl i then pPrintPrec lvl prec ty else empty), 
            (if posShowLvl i then pPrintPrec lvl prec pos else empty)
            ]
        
    pPrintPrec lvl@(PrettyLevel i) prec (Forall quants body pos ty) = 
        fsep [
            text "V" <+> foldl (\ acc hd -> acc <+> pPrintPrec lvl prec hd) empty quants <+> text "->", 
            nest 2 $ pPrintPrec lvl prec body, 
            (if typeShowLvl i then pPrintPrec lvl prec ty else empty),
            (if posShowLvl i then pPrintPrec lvl prec pos else empty)
            ]
        
    pPrintPrec lvl@(PrettyLevel i) prec (Let [(var, def)] body pos ty) = 
        fsep [
            text "let" <+> text var <+> text "=" <+> pPrintPrec lvl prec def <+> text "in", 
            nest 2 $ pPrintPrec lvl prec body, 
            (if typeShowLvl i then pPrintPrec lvl prec ty else empty),
            (if posShowLvl i then pPrintPrec lvl prec pos else empty)
            ]
        
    pPrintPrec lvl@(PrettyLevel i) prec (App fct args pos ty) =
        hsep [
            pPrintPrec lvl prec fct,
            nest 2 $ hsep $ map (\ hd -> ((case fst hd of
                                               Explicite -> id
                                               Implicite -> Pretty.braces
                                               Oracled -> Pretty.brackets
                                          ) $ pPrintPrec lvl prec $ snd hd
                                         )
                                ) args,
            (if typeShowLvl i then pPrintPrec lvl prec ty else empty),
            (if posShowLvl i then pPrintPrec lvl prec pos else empty)
            ]
        
    pPrintPrec lvl@(PrettyLevel i) prec (Case fct cases pos ty) =
        fsep [text "case" <+> pPrintPrec lvl prec fct <+> text "of", 
              foldl (\ acc ([(pat, [])], def) -> 
                     acc $+$
                     fsep [nest 2 $ text "|" <+> pPrintPrec lvl prec pat <+> text "=>", 
                           nest 4 $ pPrintPrec lvl prec def 
                          ]
                    ) empty cases,
              (if typeShowLvl i then pPrintPrec lvl prec ty else empty), 
              (if posShowLvl i then pPrintPrec lvl prec pos else empty)
             ]

-- *******************************************************************
-- Tests ...
-- *******************************************************************




main :: IO ()
main = do {
    ; let toparse = "(\\ {A B C :: Type} a -> let x = a :: A in x x {x} [case x of | _ => x | g f@(_) {y} => _]) :: V {A B C :: Type} A -> A"
    ; let sourcename = "test"
    ; let lvl = PrettyLevel 0
    ; let prec = 0
    ; let style = Style { mode = PageMode, lineLength = 80, ribbonsPerLine=1.0 }
    ; case parse (trepParser dummyPState) sourcename toparse of
        Left err -> error $ show err
        Right (term, ty) -> do {
            ; putStrLn $ toparse
            ; putStrLn $ show term
            ; putStrLn $ renderStyle style $ fsep [pPrintPrec lvl prec term, nest 2 $  pPrintPrec lvl prec ty]
            }
    }
       
       