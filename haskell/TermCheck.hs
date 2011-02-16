{-# LANGUAGE ExistentialQuantification, FlexibleInstances, RankNTypes, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, UndecidableInstances, EmptyDataDecls, PatternGuards #-}

-- 

module TermCheck where

import Def
import TypeM
import Control.Monad.Error

termcheckTerm :: Term -> TypeM Term
termcheckTerm te = error "NYI"

termcheckPattern :: Pattern -> TypeM [(Name, Term)]
termcheckPattern pat = error "NYI"

