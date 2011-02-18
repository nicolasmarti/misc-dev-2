{-# LANGUAGE ExistentialQuantification, FlexibleInstances, RankNTypes, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, UndecidableInstances, EmptyDataDecls, PatternGuards #-}

-- 

module Reduction where

import Def
import TypeM
import Control.Monad.Error
import Definition
import Unification

import LLVMBinding

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

        -- the variable is either a pattern variable, or the typechecking was not performed
        reduce' te@(AVar pos Nothing ty) = error "TODO"
        
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
            -- here we needs to reduce the quants types
            ; quants' <- error "compute quants"
            -- first push the quantifiers in the environment
            ; error "pushQuants quants"
            -- then reduce the body
            ; body' <- reduce' body
            -- then pop the quantifications           
            ; error "popQuants $ length quants"
            -- finally rebuild the term
            ; return $ Lambda quants' body' pos ty
            }
        
                                               | otherwise = return te

        -- Forall: idem as Lambda
        reduce' te@(Forall quants body pos ty) | betaStrong config = do {
            -- here we needs to reduce the quants types
            ; quants' <- error "compute quants"
            -- first push the quantifiers in the environment
            ; error "pushQuants quants"
            -- then reduce the body
            ; body' <- reduce' body
            -- then pop the quantifications           
            ; error "popQuants $ length quants"
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

        -- Case: 
        reduce' te@(Case cte cases pos ty) | iota config = do {
            -- first we reduce the term
            ; cte' <- reduce' cte
            -- the rest is to be done depending on the deltaIotaWeakness
            -- if we are betaiotaweek we simply throw an error
            -- else we keep at least the cte'          
            ; let cont = if deltaIotaWeak config then id else flip catchError (\ _ -> return $ Case cte' cases pos ty)
                      
            ; cont $ do {
                -- we look for a proper term to execute (warning: the pattern vars are pushed in the environment)
                -- by traversing the cases
                ; thecase <- traverseTypeM (\ (patterns, cont) -> do {
                                                -- we look for a pattern (and guard) that matches
                                                -- by traversing the patterns
                                                ; traverseTypeM (\ (pattern, guards, _) -> do {
                                                                     -- first unify the pattern with the term
                                                                     ; unifyPattern pattern cte'
                                                                     -- then traverse the guards to know if one is valid
                                                                     ; traverseTypeM (\ (guard, _, _) -> do {
                                                                                          ; guard' <- reduce' guard
                                                                                          ; case guard' of
                                                                                              Cste _ _ _ _ (Just (PrimitiveValue val)) | isTrue val -> return ()
                                                                                              _ -> throwError ErrNoReduciblePattern
                                                                                          }
                                                                                     ) ErrNoReduciblePattern guards
                                                                     ; return ()
                                                                     }
                                                                ) ErrNoReduciblePattern $ patterns
                                                ; return cont
                                                }                                                          
                                   ) ErrNoReduciblePattern $ cases
                -- we reduce it             
                ; reduce' thecase

                -- here the patterns of the case are still pushed in the env
                -- however the reduction on the term assure that all their instances has been reduced
                -- so we can safely pop them
                ; error "pop pattern vars"
                }
            }
                                           | otherwise = return te

        -- App: the big part ... not yet done
        reduce' te@(App fct args pos ty) = error "NYI"

