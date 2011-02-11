{-# LANGUAGE ExistentialQuantification, FlexibleInstances, RankNTypes, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, UndecidableInstances, EmptyDataDecls #-}

-- this is a little language to be compile in VM

module Trep (

             Position (..), Term(..),

             main
             
            ) where


import VM

-- position in a file
-- Nothing -> for interactive
data Position = NoPosition
              | Position (Maybe String {- file name-}, ((Int, Int), (Int, Int)))

data TypeInfo = NoType
              | Annotation Term
              | Infered Term
    
data Term = Type
          | Var Position Name (Maybe Int) TypeInfo
          | Cste Position Name TypeInfo
          
          | Lambda [Quantifier] Term Position TypeInfo
          | Forall [Quantifier] Term Position TypeInfo
          
          | Ind [Quantifier] Term [(Name, Term)] Position TypeInfo
          | Constr Int Term Position TypeInfo

          | Let [(Quantifier, Term)] Term Position TypeInfo

          | App Func [(Nature, Term)] Position TypeInfo

          | Case Term [([(Pattern, [Guard])], Term)] Position TypeInfo

          | DoNotation [DoStmt] Position TypeInfo
            
data Func = Term
          -- what is the difference ???? Notation can be inlined ...
          | Notation OpProp String Position TypeInfo Term {- the semantics-}
          | Operator OpProp String Position TypeInfo Term 
            
data OpProp = OpProp Assoc BindStrentgh            

data Assoc = Left 
           | Right

data BindStrentgh = BindStrentgh Int

data Quantifier

data Pattern

data Guard

data DoStmt 

type Name = String

data Nature = Implicite
            | Explicite
            | Oracled

main :: IO ()
main = return ()