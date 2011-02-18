{-# LANGUAGE ExistentialQuantification, FlexibleInstances, RankNTypes, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, UndecidableInstances, EmptyDataDecls, PatternGuards #-}

-- 

module Reduction where

import Def
import TypeM
import Control.Monad.Error
import Definition

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
        reduce' te@(AVar pos Nothing ty) = throwError $ ErrTermNotTypeChecked pos
        
        reduce' te@(AVar pos (Just te') ty) = reduce' te'

        -- the typechecking has not been done -> it is an error
        reduce' te@(Cste pos name ty Nothing _) = throwError $ ErrTermNotTypeChecked pos
        
        -- no delta reduction --> return it without the definition
        reduce' te@(Cste pos name ty (Just defptr) _) | not (delta config) = return $ Cste pos name ty (Just defptr) Nothing
        
        -- delta reduction --> if no def then find one
        reduce' te@(Cste pos name ty (Just defptr) Nothing) | (delta config) = do {
            ; def <- getDefinition defptr pos
            ; return $ Cste pos name ty (Just defptr) $ Just def
            }

        -- delta reduction and we have the def -> return as it
        reduce' te@(Cste pos name ty (Just defptr) (Just def)) | (delta config) = return te

        -- Lambda: with strong beta -> reduce the body, else nothing
        reduce' te@(Lambda quants body pos ty) | betaStrong config = do {
            -- first push the quantifiers in the environment
            ; error "pushQuants quants"
            -- then reduce the body
            ; body' <- reduce' body
            -- then pop the quantifications           
            ; quants' <- error "popQuants $ length quants"
            -- finally rebuild the term
            ; return $ Lambda quants' body' pos ty
            }
        
                                               | otherwise = return te

        -- Forall: idem as Lambda
        reduce' te@(Forall quants body pos ty) | betaStrong config = do {
            -- first push the quantifiers in the environment
            ; error "pushQuants quants"
            -- then reduce the body
            ; body' <- reduce' body
            -- then pop the quantifications           
            ; quants' <- error "popQuants $ length quants"
            -- finally rebuild the term
            ; return $ Forall quants' body' pos ty
            }
            
                                               | otherwise = return te
        
        -- the typechecking has not been done -> it is an error
        reduce' te@(Operator op s pos ty Nothing _) = throwError $ ErrTermNotTypeChecked pos
        
        -- we have a defptr but no def --> look for it
        reduce' te@(Operator op s pos ty (Just defptr) Nothing) = do {
            ; def <- getDefinition defptr pos
            ; return $ Operator op s pos ty (Just defptr) $ Just def
            }
        -- we have a defptr and the def --> return as it
        reduce' te@(Operator op s pos ty (Just defptr) (Just def)) = return te
        
        
        -- Do Notation: Not sure how to do that right now ...
        reduce' te@(DoNotation stmts pos ty) = error "Do Notation is not yet supported"

        -- Case: TODO
        reduce' te@(Case cte cases pos ty) | iota config = error "NYI"
                                           | otherwise = return te

        -- App: the big part ... not yet done
        reduce' te@(App fct args pos ty) = error "NYI"

