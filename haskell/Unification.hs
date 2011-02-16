{-# LANGUAGE ExistentialQuantification, FlexibleInstances, RankNTypes, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, UndecidableInstances, EmptyDataDecls, PatternGuards #-}

-- 

module Unification where

import Def
import TypeM
import Control.Monad.Error

unifyTerm :: Term -> Term -> TypeM Term
unifyTerm t1 t2 = error "NYI"

unifyPattern :: Pattern -> Term -> TypeM [(Name, Term)]
unifyPattern pat te = error "NYI"