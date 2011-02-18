{-# LANGUAGE ExistentialQuantification, FlexibleInstances, RankNTypes, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, UndecidableInstances, EmptyDataDecls, PatternGuards #-}

-- this is the main definitions for Trep

module Def where

import qualified Data.Set as Set
import qualified Data.Map as Map

import LLVMBinding

-- ************************************************************
-- Term and related
-- ************************************************************

data Position = NoPosition
              | Position (Maybe String) {- file name-} ((Int, Int), (Int, Int))
              deriving (Eq, Show, Ord)

data TypeInfo = NoType
              | Annotation Term Position
              | Infered Term
              deriving (Eq, Show, Ord)

data OpProp = OpInfix OpAssoc BindStrentgh
            | OpPrefix BindStrentgh
            | OpPostfix BindStrentgh              
              deriving (Eq, Show, Ord)

type BindStrentgh = Int

data OpAssoc = OpAssocNone
             | OpAssocLeft
             | OpAssocRight
              deriving (Eq, Show, Ord, Read)               
                       
data Quantifier = Quantifier ([(Name, Position)], TypeInfo, Nature)
                deriving (Eq, Show, Ord)

data Pattern = PAVar Position TypeInfo
             | PCste Position Name TypeInfo (Maybe DefPtr)
             | PVar Position Name TypeInfo
             | PApp Name (Maybe DefPtr) [(Nature, Pattern)] Position TypeInfo
             | PAlias Position Name Pattern TypeInfo
             deriving (Eq, Show, Ord)

type Guard = (Term, Position, TypeInfo)

data DoStmt = DoLet Name Position TypeInfo Term
            | DoBind Name Position TypeInfo Term
            | DoVal Term Position TypeInfo
            deriving (Eq, Show, Ord)

type Name = String

data Nature = Hidden
            | Explicite
            | Implicit
            deriving (Eq, Show, Ord)

data Term = Type Position TypeInfo

            -- the correct index is set at typecheck time
          | Var Position Name (Maybe Int) TypeInfo

            -- the correct term is set at typecheck time
          | AVar Position (Maybe Term) TypeInfo

          -- the proper implementation path is set at typecheck time
          -- the defptr is aliased (it is the result of the typechecking, hence context sensitive)
          -- the definition is only for reduction needed by the typechecker
          | Cste Position Name TypeInfo (Maybe DefPtr) (Maybe Definition)

          | Lambda [Quantifier] Term Position TypeInfo
          | Forall [Quantifier] Term Position TypeInfo

          | Let [(Name, Term)] Term Position TypeInfo

          | App Term [(Nature, Term)] Position TypeInfo

          -- the Maybe Term is for recopying the Term in order to properly TypeCheck 
          -- this is not more necessary as we have now a representation for Pattern Var (+ ref in Env
          | Case Term [([(Pattern, [Guard], Maybe Term)], Term)] Position TypeInfo

          | DoNotation [DoStmt] Position TypeInfo

          -- the proper implementation path is set at typecheck time
          -- the defptr is aliased (it is the result of the typechecking, hence context sensitive)            
          -- the definition is only for reduction needed by the typechecker
          | Operator OpProp String Position TypeInfo (Maybe DefPtr) (Maybe Definition)
          deriving (Eq, Show, Ord)

-- ************************************************************
-- Definition: constituant of a module
-- ************************************************************

data Definition = DefSig Name Position Term
                | DefCase Name [([(Pattern, [Guard], Maybe Term)], Term)] Position TypeInfo

                | DefInductive Name [Quantifier] Term [(Name, Term)] Position TypeInfo
                | DefConstr Name Int Position TypeInfo

                | DefNotation String OpProp
                  
                  -- this one does not appear in a module
                  -- just to be use in Cste
                  -- primitives are LLVM (constante) value 
                | PrimitiveValue LLVMValue

                deriving (Eq, Show, Ord)


-- ************************************************************
-- module: build and typechecked
-- ************************************************************

type ModulePath = [Name]

data TCModule = TCModule ModulePath (Map.Map Name Definition)
           deriving (Eq, Show, Ord)

type DefPtr = (ModulePath, Name)

-- *******************************************************************************
-- environment: represent the working data structure for currently building module
-- *******************************************************************************

type Substitution = Map.Map Int Term

data TCEnv = TCEnv { 
    
    -- quantified variables, index >= 0
    qv :: [Quantifier],
    
    -- free variable, index < 0
    fv :: [(Name, Maybe Term)],
    
    -- pattern variable, index == Nothing
    pv :: [(Name, Term)],
    
    -- the sum of substitution
    subst :: Substitution,
    
    -- substituable variable, only used for unification
    sv :: Set.Set Int,

    -- this is for keeping track of size equation (for terminaison checking)
    sizeEq :: (),

    -- destruction equation, needed for reasoning on dependent types
    destructEq :: [(Term, Term)],

    -- term storage, for keeping currently working terms, in order to have unification propagated on all the typechecking tree
    termStorage :: [[Term]],

    -- definitions (prototypes + cases + ...)
    def :: Map.Map Name Definition,
    
    -- the imports: a mapping from alias path to real module path
    moduleAlias :: Map.Map ModulePath (Set.Set ModulePath)
    
    }
           deriving (Eq, Show, Ord)

-- *******************************************************************************
-- global: a global set of values used for typechecking / unification / ...
-- *******************************************************************************

data ModuleTree = ModuleDir (Map.Map Name ModuleTree)
                | ModuleDef TCModule
                deriving (Eq, Show, Ord)


data TCGlobal = TCGlobal {
    
    -- the available modules
    moduleTree :: ModuleTree

    }
              deriving (Eq, Show, Ord)

