{-# LANGUAGE ExistentialQuantification, FlexibleInstances, RankNTypes, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, UndecidableInstances, EmptyDataDecls, PatternGuards #-}

-- 

module Unification where

import Def
import TypeM
import Control.Monad.Error

unifyTerm :: Term -> Term -> TypeM Term
unifyTerm t1 t2 = error "NYI"

-- the pattern variables are directly pushed in the env, thus return ()
unifyPattern :: Pattern -> Term -> TypeM ()
unifyPattern pat te = error "NYI"

