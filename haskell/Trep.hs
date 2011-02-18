{-# LANGUAGE ExistentialQuantification, FlexibleInstances, RankNTypes, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, UndecidableInstances, EmptyDataDecls, PatternGuards #-}

-- 

module Trep (main) where


import Def
import TypeM
import Parser
import Pprinter
import Env
import Definition
import Reduction
import Unification
import TermCheck

main :: IO ()
main = return ()