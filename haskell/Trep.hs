{-# LANGUAGE ExistentialQuantification, FlexibleInstances, RankNTypes, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, UndecidableInstances #-}

-- this is a little language to be compile in VM

module Trep (

             Position (..), TrepAST(..),

             main
             
            ) where


import VM

-- position in a file
-- Nothing -> for interactive
data Position = Position (Maybe String {- file name-}, ((Int, Int), (Int, Int)))

-- the language AST
data TrepAST = Var Position String



main :: IO ()
main = return ()