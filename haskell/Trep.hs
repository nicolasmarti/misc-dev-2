{-# LANGUAGE ExistentialQuantification, FlexibleInstances, RankNTypes, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, UndecidableInstances, EmptyDataDecls, PatternGuards #-}

-- this is a little language to be compile in VM

module Trep (main) where


import Def
import TypeM
import Parser
import Pprinter


main :: IO ()
main = return ()