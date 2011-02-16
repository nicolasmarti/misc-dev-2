{-# LANGUAGE ExistentialQuantification, FlexibleInstances, RankNTypes, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, UndecidableInstances, EmptyDataDecls, PatternGuards #-}

-- this is the main definitions for Trep

module Def where

import qualified Data.Set as Set
import qualified Data.Map as Map

-- ************************************************************
-- Term and related
-- ************************************************************

data Position = NoPosition
              | Position (Maybe String) {- file name-} ((Int, Int), (Int, Int))
              deriving (Eq, Show, Ord, Read)

data TypeInfo = NoType
              | Annotation Term Position
              | Infered Term
              deriving (Eq, Show, Ord, Read)

data OpProp = OpInfix OpAssoc BindStrentgh
            | OpPrefix BindStrentgh
            | OpPostfix BindStrentgh              
              deriving (Eq, Show, Ord, Read)

type BindStrentgh = Int

data OpAssoc = OpAssocNone
             | OpAssocLeft
             | OpAssocRight
              deriving (Eq, Show, Ord, Read)               
                       
data Quantifier = Quantifier ([(Name, Position)], TypeInfo, Nature)
                deriving (Eq, Show, Ord, Read)

data Pattern = PAVar Position TypeInfo
             | PCste Position [Name] TypeInfo
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

data Nature = Hidden
            | Explicite
            | Implicit
            deriving (Eq, Show, Ord, Read)

data Term = Type Position TypeInfo

            -- the correct index is set at typecheck time
          | Var Position Name (Maybe Int) TypeInfo

            -- the correct term is set at typecheck time
          | AVar Position (Maybe Term) TypeInfo

          -- the proper implementation path is set at typecheck time
          | Cste Position [Name] TypeInfo (Maybe [Name])

          | Lambda [Quantifier] Term Position TypeInfo
          | Forall [Quantifier] Term Position TypeInfo

          | Let [(Name, Term)] Term Position TypeInfo

          | App Term [(Nature, Term)] Position TypeInfo

            {- the Maybe Term is for recopying the Term in order to properly TypeCheck -}
          | Case Term [([(Pattern, [Guard], Maybe Term)], Term)] Position TypeInfo

          | DoNotation [DoStmt] Position TypeInfo

          -- the proper implementation path is set at typecheck time
          | Operator OpProp String Position TypeInfo (Maybe [Name])
          deriving (Eq, Show, Ord, Read)

-- ************************************************************
-- Definition: constituant of a module
-- ************************************************************

data Definition = DefSig Name Position Term
                | DefCase Name [([(Pattern, [Guard], Maybe Term)], Term)] Position TypeInfo

                | DefInductive Name [Quantifier] Term [(Name, Term)] Position TypeInfo
                | DefConstr Name Int Term Position TypeInfo

                | DefTypeClass Name [Quantifier] Term [(Name, Term, Maybe Term)] Position TypeInfo
                | DefInstance Name [Quantifier] Term [(Name, [([(Pattern, [Guard], Maybe Term)], Term)])] Position TypeInfo

                | DefOracle Name [([(Pattern, [Guard], Maybe Term)], Term)] Position TypeInfo

                | DefNotation String OpProp

                deriving (Eq, Show, Ord, Read)


-- ************************************************************
-- module: build and typechecked
-- ************************************************************

data TCModule = TCModule ModulePath (Map.Map Name Definition)
           deriving (Eq, Show, Ord, Read)

-- *******************************************************************************
-- environment: represent the working data structure for currently building module
-- *******************************************************************************

type Substitution = Map.Map Int Term

type ModulePath = [Name]

data TCEnv = TCEnv { 
    
    -- quantified variables
    qv :: [Quantifier],
    fv :: [(Name, Maybe Term)],
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
           deriving (Eq, Show, Ord, Read)

-- *******************************************************************************
-- global: a global set of values used for typechecking / unification / ...
-- *******************************************************************************

data ModuleTree = ModuleDir (Map.Map Name ModuleTree)
                | ModuleDef TCModule
                deriving (Eq, Show, Ord, Read)


data TCGlobal = TCGlobal {
    
    -- the available modules
    moduleTree :: ModuleTree

    }
              deriving (Eq, Show, Ord, Read)

