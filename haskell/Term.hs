{-# LANGUAGE ExistentialQuantification, FlexibleInstances, RankNTypes, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, UndecidableInstances, EmptyDataDecls, PatternGuards #-}

-- 

module Term where

import Def

import Data.Ratio

-- Warning: this overwrite the previous type info
addAnnotation :: Term -> Term -> Term
addAnnotation te ty = addTypeInfo te ty'
    where
        ty' :: TypeInfo 
        ty' = Annotation ty NoPosition
        
addTypeInfo :: Term -> TypeInfo -> Term
addTypeInfo (Type pos _) ty = Type pos ty
addTypeInfo (AVar pos mt _) ty = AVar pos mt ty
addTypeInfo (Cste pos name _ md mt) ty = Cste pos name ty md mt
addTypeInfo (Lambda qs body pos _) ty = Lambda qs body pos ty
addTypeInfo (Forall qs body pos _) ty = Forall qs body pos ty        
        
termPrec :: Term -> BindStrentgh
termPrec (Operator op _ _ _ _ _) = opPrec op
termPrec (Var _ _ _ _) = 100
termPrec (Cste _ _ _ _ _) = 100
termPrec (AVar _ _ _) = 100
termPrec (App (Operator (OpInfix assoc opprec) _ _ _ _ _) args _ _) | args' <- filter (\ (nat, _) -> nat == Explicite) args, length args' == 2 = opprec
termPrec (App (Operator (OpPrefix opprec) _ _ _ _ _) args _ _) | args' <- filter (\ (nat, _) -> nat == Explicite) args, length args' == 1 = opprec
termPrec (App (Operator (OpPostfix opprec) _ _ _ _ _) args _ _) | args' <- filter (\ (nat, _) -> nat == Explicite) args, length args' == 1 = opprec
termPrec (App _ _ _ _) = -1
termPrec _ = -2

termAssoc :: Term -> OpAssoc
termAssoc (Operator op _ _ _ _ _) = opAssoc op
termAssoc (App (Operator (OpInfix assoc opprec) _ _ _ _ _) args _ _) | args' <- filter (\ (nat, _) -> nat == Explicite) args, length args' == 2 = assoc
termAssoc (App (Operator (OpPrefix opprec) _ _ _ _ _) args _ _) | args' <- filter (\ (nat, _) -> nat == Explicite) args, length args' == 1 = OpAssocNone
termAssoc (App (Operator (OpPostfix opprec) _ _ _ _ _) args _ _) | args' <- filter (\ (nat, _) -> nat == Explicite) args, length args' == 1 = OpAssocNone
termAssoc (App _ _ _ _) = OpAssocRight
termAssoc _ = OpAssocNone

opPrec :: OpProp -> BindStrentgh
opPrec (OpInfix _ s) = fromIntegral s
opPrec (OpPrefix s) = fromIntegral s
opPrec (OpPostfix s) = fromIntegral s

opAssoc :: OpProp -> OpAssoc
opAssoc (OpInfix s _) = s
opAssoc (OpPrefix s) = OpAssocNone
opAssoc (OpPostfix s) = OpAssocNone

termRationalPrec :: Term -> Rational
termRationalPrec te = composeRational (termPrec te, termAssoc te)

decomposeRational :: Rational -> (BindStrentgh, OpAssoc)
decomposeRational r = (fromIntegral $ numerator r, 
                       case denominator r of 
                           3557 -> OpAssocNone
                           3559 -> OpAssocRight
                           3571 -> OpAssocLeft
                      )
                      
composeRational :: (BindStrentgh, OpAssoc) -> Rational
composeRational (prec, assoc) = (fromIntegral prec) % (case assoc of 
                                          OpAssocNone -> 3557
                                          OpAssocRight -> 3559
                                          OpAssocLeft -> 3571
                                       )
