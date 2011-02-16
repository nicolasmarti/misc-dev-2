{-# LANGUAGE ExistentialQuantification, FlexibleInstances, RankNTypes, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, UndecidableInstances, EmptyDataDecls, PatternGuards #-}

-- 

module Reduction where

import Def
import TypeM
import Control.Monad.Error

data ReductionStrategy = Lazy
                       | Eager
                         
data ReductionConfig = ReductionConfig {
    -- lazy or eager
    strat:: ReductionStrategy,
    -- beta reduction (lambda with app)
    beta:: Bool,
    -- strong beta reduction (reduction under quantifier)
    betaStrong:: Bool,
    -- unfold definition in Cste Term and reduce on them
    delta:: Bool,
    -- reduce case of
    iota:: Bool,
    -- if a iota reduction leads to a not exec case of --> backtrack before unfolding (== simpl reduction tactic of Coq)
    deltaIotaWeak:: Bool,
    -- reduce the let
    zeta:: Bool,
    -- eta reduction ( \x. f x --> f | x not free in f)
    eta:: Bool
    }

reduceTerm :: Term -> ReductionConfig -> TypeM Term
reduceTerm te config = reduce' te
    where
        reduce' :: Term -> TypeM Term
        reduce' te@(Type _ _) = return te
        
        reduce' te@(Var pos name index ty) | Just index' <- index, index' < 0 = return te
                                           | Just index' <- index, index' >= 0 = return te
                                           | Nothing <- index = return te

        -- the typechecking has not been done -> it is an error
        reduce' te@(Cste pos name ty Nothing) = throwError $ ErrTermNotTypeChecked pos

        -- 
        reduce' te@(Lambda quants body pos ty) | betaStrong config = error "NYI"
                                               | otherwise = return te

        reduce' te@(Forall quants body pos ty) | betaStrong config = error "NYI"
                                               | otherwise = return te

        reduce' te@(App fct args pos ty) = error "NYI"

        reduce' te@(Case cte cases pos ty) | iota config = error "NYI"
                                           | otherwise = return te

        -- 
        reduce' te@(DoNotation stmts pos ty) = error "NYI"

        -- the typechecking has not been done -> it is an error
        reduce' te@(Operator op s pos ty Nothing) = throwError $ ErrTermNotTypeChecked pos
