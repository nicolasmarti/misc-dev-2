{-# LANGUAGE ExistentialQuantification, FlexibleInstances, RankNTypes, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, UndecidableInstances, EmptyDataDecls, PatternGuards #-}

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
import Data.Ratio

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

            {- the Maybe Term is for recopying the Term in order to properly TypeCheck -}
          | Case Term [([(Pattern, [Guard], Maybe Term)], Term)] Position TypeInfo

          | DoNotation [DoStmt] Position TypeInfo

          | Operator OpProp String Position TypeInfo
          deriving (Eq, Show, Ord, Read)

termPrec :: Term -> BindStrentgh
termPrec (Operator op _ _ _) = opPrec op
termPrec (Var _ _ _ _) = 100
termPrec (Cste _ _ _ _) = 100
termPrec (AVar _ _ _) = 100
termPrec (App (Operator (OpInfix assoc opprec) _ _ _) args _ _) | args' <- filter (\ (nat, _) -> nat == Explicite) args, length args' == 2 = opprec
termPrec (App (Operator (OpPrefix opprec) _ _ _) args _ _) | args' <- filter (\ (nat, _) -> nat == Explicite) args, length args' == 1 = opprec
termPrec (App (Operator (OpPostfix opprec) _ _ _) args _ _) | args' <- filter (\ (nat, _) -> nat == Explicite) args, length args' == 1 = opprec
termPrec (App _ _ _ _) = -1
termPrec _ = -2

termAssoc :: Term -> OpAssoc
termAssoc (Operator op _ _ _) = opAssoc op
termAssoc (App (Operator (OpInfix assoc opprec) _ _ _) args _ _) | args' <- filter (\ (nat, _) -> nat == Explicite) args, length args' == 2 = assoc
termAssoc (App (Operator (OpPrefix opprec) _ _ _) args _ _) | args' <- filter (\ (nat, _) -> nat == Explicite) args, length args' == 1 = OpAssocNone
termAssoc (App (Operator (OpPostfix opprec) _ _ _) args _ _) | args' <- filter (\ (nat, _) -> nat == Explicite) args, length args' == 1 = OpAssocNone
termAssoc (App _ _ _ _) = OpAssocRight
termAssoc _ = OpAssocNone

data OpProp = OpInfix OpAssoc BindStrentgh
            | OpPrefix BindStrentgh
            | OpPostfix BindStrentgh              
              deriving (Eq, Show, Ord, Read)

type BindStrentgh = Int

opPrec :: OpProp -> BindStrentgh
opPrec (OpInfix _ s) = fromIntegral s
opPrec (OpPrefix s) = fromIntegral s
opPrec (OpPostfix s) = fromIntegral s

opAssoc :: OpProp -> OpAssoc
opAssoc (OpInfix s _) = s
opAssoc (OpPrefix s) = OpAssocNone
opAssoc (OpPostfix s) = OpAssocNone

decomposeRational :: Rational -> (BindStrentgh, OpAssoc)
decomposeRational r = (fromIntegral $ numerator r, 
                       case denominator r of 
                           3557 -> OpAssocNone
                           3559 -> OpAssocRight
                           3571 -> OpAssocLeft
                      )
                      
composeRational :: (BindStrentgh, OpAssoc) -> Rational
composeRational (prec, assoc) = (fromIntegral prec) % (case assoc of 
                                          OpAssocNone -> 3557
                                          OpAssocRight -> 3559
                                          OpAssocLeft -> 3571
                                       )

termRationalPrec :: Term -> Rational
termRationalPrec te = composeRational (termPrec te, termAssoc te)

data OpAssoc = OpAssocNone
             | OpAssocLeft
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


data TopLevel = DefSig Name Position TypeInfo
              | DefCase Name [([(Pattern, [Guard], Maybe Term)], Term)] Position

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
    operators :: [(String, OpProp)]
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
                        <|> try (parens myTokenParser $ parseTerm)

        parseTermLvl2 :: Parser Term
        parseTermLvl2 = try parseApp
                        <|> parseTermLvl1

        parseType :: Parser Term
        parseType = do {
            ; whiteSpace myTokenParser
            ; (_, pos) <- withPosition $ reserved myTokenParser "Type"
            ; whiteSpace myTokenParser                          
            ; return (Type pos)
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
                      ; return $ Quantifier ([res], NoType, Implicite)
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
                                             ; return (Implicite, arg)
                                             }
                                         )
                                 <|> try (do { arg <- squares myTokenParser parseTerm
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
                                                                                            (App (Operator o s pos NoType) [(Explicite, t1), (Explicite, t2)] (Position src1 (start1, end2)) NoType, (Position src1 (start1, end2)))
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
                                                                                        (App (Operator o s pos NoType) [(Explicite, t)] (Position src (starto, end)) NoType, (Position src (starto, end)))
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
            ; return $ Operator o s pos ty
            }


-- precision is an Int
-- using bits ...
-- 1: show types
-- 2: show position

typeShowLvl :: Int -> Bool
typeShowLvl = flip testBit 0

posShowLvl :: Int -> Bool
posShowLvl = flip testBit 1

impliciteShowLvl :: Int -> Bool
impliciteShowLvl = flip testBit 2

oracledShowLvl :: Int -> Bool
oracledShowLvl = flip testBit 3

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
    pPrintPrec lvl prec (PApp fct args pos ty) = 
        text fct  
        <+> foldl (\ acc hd -> acc <+> ((case fst hd of
                                             Explicite -> id
                                             Implicite -> Pretty.braces
                                             Oracled -> Pretty.brackets
                                        ) $ pPrintPrec lvl prec $ snd hd
                                       )
                  ) empty args
    pPrintPrec lvl prec (PAlias _ name underp _) = text name <> text "@" <> Pretty.parens (pPrintPrec lvl prec underp)


-- False Left, True right
needParens :: Rational -> Term -> Bool
needParens r te = 
    let (prec, assoc) = decomposeRational r in
    let precte = termPrec te in
    let assocte = termAssoc te in
    if (precte < prec || (precte == prec && assocte == OpAssocRight)) then True else False

lowPrec :: Rational
lowPrec = (-1000) % 3557

instance Pretty Term where
    pPrintPrec lvl@(PrettyLevel i) prec te@(Type pos) = 
        (if needParens prec te then Pretty.parens else id)
        (text "Type" <+> (if posShowLvl i then pPrintPrec lvl prec pos else empty))

    pPrintPrec lvl@(PrettyLevel i) prec  te@(Var pos name debruijn ty) = 
        (if needParens prec te then Pretty.parens else id)
        (text name <+> (if typeShowLvl i then pPrintPrec lvl prec ty else empty) <> (if posShowLvl i then pPrintPrec lvl prec pos else empty))

    pPrintPrec lvl@(PrettyLevel i) prec  te@(AVar pos _ ty) = 
        (if needParens prec te then Pretty.parens else id)
        (text "_" <+> (if typeShowLvl i then pPrintPrec lvl prec ty else empty) <+> (if posShowLvl i then pPrintPrec lvl prec pos else empty))

    pPrintPrec lvl@(PrettyLevel i) prec  te@(Lambda quants body pos ty) = 
        (if needParens prec te then Pretty.parens else id)
        (fsep [
            text "\\" <+> foldl (\ acc hd -> acc <+> pPrintPrec lvl prec hd) empty quants <+> text "->", 
            nest 2 $ pPrintPrec lvl lowPrec body, 
            (if typeShowLvl i then pPrintPrec lvl prec ty else empty), 
            (if posShowLvl i then pPrintPrec lvl prec pos else empty)
            ]
        )

    pPrintPrec lvl@(PrettyLevel i) prec  te@(Forall quants body pos ty) = 
        (if needParens prec te then Pretty.parens else id)
        (fsep [
            text "V" <+> foldl (\ acc hd -> acc <+> pPrintPrec lvl lowPrec hd) empty quants <+> text "->", 
            nest 2 $ pPrintPrec lvl prec body, 
            (if typeShowLvl i then pPrintPrec lvl prec ty else empty),
            (if posShowLvl i then pPrintPrec lvl prec pos else empty)
            ])

    pPrintPrec lvl@(PrettyLevel i) prec te@(Let [(var, def)] body pos ty) = 
        (if needParens prec te then Pretty.parens else id)
        (fsep [
            text "let" <+> text var <+> text "=" <+> pPrintPrec lvl lowPrec def <+> text "in", 
            nest 2 $ pPrintPrec lvl lowPrec body, 
            (if typeShowLvl i then pPrintPrec lvl prec ty else empty),
            (if posShowLvl i then pPrintPrec lvl prec pos else empty)
            ])
    
    pPrintPrec lvl@(PrettyLevel i) prec te@(App op@(Operator (OpInfix assoc opprec) s pos1 ty1) args pos2 ty2) | args' <- filter (\ (nat, _) -> nat == Explicite) args, length args' == 2 =        
        (if needParens prec te then Pretty.parens else id)
        (hsep [pPrintPrec lvl (termRationalPrec te) $ snd (args'!!0), text s, pPrintPrec lvl (termRationalPrec te) $ snd (args'!!1)])

    pPrintPrec lvl@(PrettyLevel i) prec te@(App op@(Operator (OpPrefix opprec) s pos1 ty1) args pos2 ty2) | args' <- filter (\ (nat, _) -> nat == Explicite) args, length args' == 1 =        
        (if needParens prec te then Pretty.parens else id)
        (hsep [text s, pPrintPrec lvl (termRationalPrec te) $ snd (args'!!0)])

    pPrintPrec lvl@(PrettyLevel i) prec te@(App op@(Operator (OpPostfix opprec) s pos1 ty1) args pos2 ty2) | args' <- filter (\ (nat, _) -> nat == Explicite) args, length args' == 1 =        
        (if needParens prec te then Pretty.parens else id)
        (hsep [pPrintPrec lvl (termRationalPrec te) $ snd (args'!!0), text s])
    
    pPrintPrec lvl@(PrettyLevel i) prec (te@(Operator o s pos ty)) =
        Pretty.parens $ text s

    pPrintPrec lvl@(PrettyLevel i) prec te@(App fct args pos ty) =
        (if needParens prec te then Pretty.parens else id)
        (hsep [
            pPrintPrec lvl prec fct,
            nest 2 $ hsep $ map (\ hd -> ((case fst hd of
                                               Explicite -> (if (needParens (termRationalPrec te) $ snd hd) then Pretty.parens else id) $ pPrintPrec lvl lowPrec $ snd hd
                                               Implicite -> if impliciteShowLvl i then Pretty.braces $ pPrintPrec lvl lowPrec $ snd hd else empty
                                               Oracled -> if oracledShowLvl i then Pretty.brackets $ pPrintPrec lvl lowPrec $ snd hd else empty
                                          ) 
                                         )
                                ) args,
            (if typeShowLvl i then pPrintPrec lvl prec ty else empty),
            (if posShowLvl i then pPrintPrec lvl prec pos else empty)
            ])

    pPrintPrec lvl@(PrettyLevel i) prec te@(Case fct cases pos ty) =
        (if needParens prec te then Pretty.parens else id)
        (fsep [text "case" <+> pPrintPrec lvl lowPrec fct <+> text "of", 
              foldl (\ acc (cases, def) -> 
                     acc $+$ foldl ( \ acc (pat, guards, _) -> acc $+$ fsep [nest 2 $ text "|" <+> pPrintPrec lvl lowPrec pat <+> foldl (\ acc (g, _, _) -> acc $+$ text "where" <+> pPrintPrec lvl lowPrec g) empty guards <+> text "=>" <+> pPrintPrec lvl lowPrec def]) empty cases
                    ) empty cases,
              (if typeShowLvl i then pPrintPrec lvl prec ty else empty), 
              (if posShowLvl i then pPrintPrec lvl prec pos else empty)
             ])


-- *******************************************************************
-- reduction, unification, typeChecking
-- *******************************************************************

-- an environment -> valid for a module

data Environment = Environment { 
    -- quantified variables
    qv :: [(Name, Term, Nature)],
    fv :: [(Name, Maybe Term)]
    }


-- *******************************************************************
-- Tests ...
-- *******************************************************************




main :: IO ()
main = do {
    ; let toparse = "(\\ {A B C :: Type} a -> let x = a :: A in x x {x} [y + case x of | g f@(_) {y} where True where False | d {y}=> _ | _ where True => (+) x]) :: V {A B C :: Type} A -> A"
    ; let toparse1 = "~ (True && (f > s || False))"
    ; let toparse2 = "a + (b + c) * d"          
    ; let sourcename = "test"
    ; let lvl = PrettyLevel $ 4 + 8
    ; let prec = lowPrec
    ; let style = Style { mode = PageMode, lineLength = 100, ribbonsPerLine=1.0 }
    ; let parserState = ParseState { operators = [("+", OpInfix OpAssocLeft 10), ("*", OpInfix OpAssocLeft 11), (">", OpInfix OpAssocLeft 9), ("||", OpInfix OpAssocLeft  6), ("&&", OpInfix OpAssocLeft 7), ("~", OpPrefix 8)] }
    ; case parse (trepParser parserState) sourcename toparse of
        Left err -> error $ show err
        Right (term, ty) -> do {
            ; putStrLn $ toparse
            ; putStrLn $ show term
            ; putStrLn $ renderStyle style $ fsep [pPrintPrec lvl prec term, nest 2 $  pPrintPrec lvl prec ty]
            }
    }

