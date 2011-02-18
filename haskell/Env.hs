{-# LANGUAGE ExistentialQuantification, FlexibleInstances, RankNTypes, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, UndecidableInstances, EmptyDataDecls, PatternGuards #-}

-- 

module Env where

import Def
import TypeM

import Control.Monad.State
import Control.Monad.Error

import Data.Map as Map

getEnv :: TypeM TCEnv
getEnv = get

setEnv :: TCEnv -> TypeM ()
setEnv = put

-- grab a TCModule from a ModuleTree given a path
getTCModule :: ModulePath -> ModuleTree -> TypeM TCModule
getTCModule path tree = catchError (getTCModule' path tree) (\ (ErrNoModule _ _) -> throwError $ ErrNoModule path NoPosition)
    where
        getTCModule' [] (ModuleDef mod) = return mod
        getTCModule' path@(hd:tl) (ModuleDir dir) = (case Map.lookup hd dir of
                                              Nothing -> throwError $ ErrNoModule path NoPosition
                                              Just tree' -> getTCModule' tl tree'
                                         )
        getTCModule' path tree = throwError $ ErrNoModule path NoPosition