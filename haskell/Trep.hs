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

import Text.PrettyPrint.HughesPJ
import Text.PrettyPrint.HughesPJClass

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

          | Let [(Quantifier, Term)] Term Position TypeInfo

          | App Term [(Nature, Term)] Position TypeInfo

          | Case Term [([(Pattern, [Guard])], Term)] Position TypeInfo

          | DoNotation [DoStmt] Position TypeInfo
            
          | Notation OpProp String Position TypeInfo Term 
            
          | Operator OpProp String Position TypeInfo Term 
          deriving (Eq, Show, Ord, Read)

data OpProp = OpProp OpAssoc BindStrentgh            
            deriving (Eq, Show, Ord, Read)
                     
type BindStrentgh = Int
                           
data OpAssoc = OpAssocLeft 
             | OpAssocRight
             deriving (Eq, Show, Ord, Read)
                      
type Quantifier = ([Name], Term, Nature)
                         
data Pattern = PAVar Position TypeInfo
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
                      "where"]
    }

-- the state for parsing :
data ParseState = ParseState {
    operators :: OperatorTable Char () Term
    }

dummyPState :: ParseState
dummyPState = ParseState { operators = [] }

trepParser :: ParseState -> Parser Term
trepParser st = parseTerm <?> "Expected a Term"
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

        withTypeInfo :: Parser a -> Parser (a, TypeInfo)
        withTypeInfo p = do {
            ; res <- p
            ; let annotparser = optionMaybe $ try $ do {
                      ; whiteSpace myTokenParser
                      ; reservedOp myTokenParser "::"
                      ; whiteSpace myTokenParser
                      ; (ty, pos) <- withPosition parseTerm
                      ; return $ Annotation ty pos
                      }
            ; tryannot <- annotparser
            ; case tryannot of
                Nothing -> return (res, NoType)
                Just ty -> return (res, ty)
            }

        parseTerm :: Parser Term
        parseTerm = parseType <|> parseVar

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
            ; return (Var pos s Nothing ty)
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
    pPrintPrec lvl prec (Annotation te pos) = text "::" <> pPrintPrec lvl prec te
    pPrintPrec lvl prec (Infered te) = text ":?:" <> pPrintPrec lvl prec te


instance Pretty Term where
    pPrintPrec lvl@(PrettyLevel i) prec (Type pos) = text "Type" <> (if posShowLvl i then pPrintPrec lvl prec pos else empty)
    pPrintPrec lvl@(PrettyLevel i) prec (Var pos name debruijn ty) = text name <> (if typeShowLvl i then pPrintPrec lvl prec ty else empty) <> (if posShowLvl i then pPrintPrec lvl prec pos else empty)


-- *******************************************************************
-- Tests ...
-- *******************************************************************


main :: IO ()
main = do { 
    ; let toparse = "v :: Type."
    ; let sourcename = "test"
    ; let lvl = PrettyLevel 3
    ; let prec = 0
    ; case parse (trepParser dummyPState) sourcename toparse of
        Left err -> error $ show err
        Right term -> do {
            ; putStrLn $ toparse
            ; putStrLn $ show term
            ; putStrLn $ render $ pPrintPrec lvl prec term
            }
    }