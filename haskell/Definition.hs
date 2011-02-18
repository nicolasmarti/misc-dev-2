{-# LANGUAGE ExistentialQuantification, FlexibleInstances, RankNTypes, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, UndecidableInstances, EmptyDataDecls, PatternGuards #-}

-- 

module Definition where

import Def
import TypeM
import Env

import Data.Maybe(fromMaybe)
import Data.Map as Map
import Data.Set as Set
import Control.Monad.Error
import Control.Monad.Reader

-- lookup a path in th

-- merge several definition into the same one
-- (verifying type consistency)
mergeDefinitions :: [Definition] -> TypeM Definition
mergeDefinitions = error "NYI"

-- get a merged definition from a def pointer
-- used in reduction
getDefinition :: DefPtr -> Position -> TypeM Definition
getDefinition (path, name) pos = do {
    ; env <- getEnv
    -- first grab local def, incase the modulepath is []
    ; let localdef = if path == [] then case Map.lookup name (def env) of Nothing -> []  
                                                                          Just d -> [d]  else []
    -- then we grab all the def in the imported module
    -- first we grab the set of module path from the alias
    ; modulepathes <- (case Map.lookup path (moduleAlias env) of
                           Nothing -> throwError $ ErrNoModule path pos
                           Just modulepathes -> return modulepathes
                      )
    -- we just grab all the definitions                  
    ; listdefs <- foldM (\ acc hd -> flip catchError (\ _ -> return acc) $ do {
                             ; moduletree <- ask >>= return . moduleTree 
                             ; (TCModule _ modmap) <- getTCModule hd moduletree 
                             ; case Map.lookup name modmap of
                                 Nothing -> return acc
                                 Just def -> return $ def:acc
                             }
                        ) [] $ Set.toList modulepathes
    ; mergeDefinitions $ localdef ++ listdefs
    }
