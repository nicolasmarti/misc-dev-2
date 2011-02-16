{-# LANGUAGE ExistentialQuantification, FlexibleInstances, RankNTypes, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, UndecidableInstances, EmptyDataDecls, PatternGuards #-}



module Pprinter where

import Def
import Term

import Text.PrettyPrint.HughesPJ
import Text.PrettyPrint.HughesPJClass

import qualified Text.PrettyPrint.HughesPJ as Pretty(char, parens, braces, brackets)
import qualified Text.PrettyPrint.HughesPJClass as Pretty(char, parens, braces, brackets)

import Data.Bits
import Data.Ratio
import Data.List(intercalate)

typeShowLvl :: Int -> Bool
typeShowLvl = flip testBit 0

posShowLvl :: Int -> Bool
posShowLvl = flip testBit 1

impliciteShowLvl :: Int -> Bool
impliciteShowLvl = flip testBit 2

oracledShowLvl :: Int -> Bool
oracledShowLvl = flip testBit 3

instance Pretty Position where
    pPrintPrec lvl prec NoPosition = empty
    pPrintPrec lvl prec (Position src ((startline, startcol), (endline, endcol))) = (maybe empty (\ s -> text "@" <> text s <> text ":") src) <> int startline <> text ":" <> int startcol <> text "-" <> int endline <> text ":" <> int endcol

instance Pretty TypeInfo where
    pPrintPrec lvl prec NoType = empty
    pPrintPrec lvl prec (Annotation te pos) = text "::" <+> pPrintPrec lvl prec te
    pPrintPrec lvl prec (Infered te) = text ":?:" <+> pPrintPrec lvl prec te

instance Pretty Quantifier where
    pPrintPrec lvl prec (Quantifier ([(var, pos)], NoType, Hidden)) = text var
    pPrintPrec lvl prec (Quantifier (vars, ty, Explicite)) = Pretty.parens $ foldl (<+>) empty (map (text . fst) vars) <+> (pPrintPrec lvl prec ty)
    pPrintPrec lvl prec (Quantifier (vars, ty, Hidden)) = Pretty.braces $ foldl (<+>) empty (map (text . fst) vars) <+> (pPrintPrec lvl prec ty)
    pPrintPrec lvl prec (Quantifier (vars, ty, Implicit)) = Pretty.brackets $ foldl (<+>) empty (map (text . fst) vars) <+> (pPrintPrec lvl prec ty)


instance Pretty Pattern where
    pPrintPrec lvl prec (PAVar _ _) = text "_"
    pPrintPrec lvl prec (PCste _ name _ _) = text name
    pPrintPrec lvl prec (PVar _ name _) = text name
    pPrintPrec lvl prec (PApp fct _ args pos ty) = 
        text fct  
        <+> foldl (\ acc hd -> acc <+> ((case fst hd of
                                             Explicite -> id
                                             Hidden -> Pretty.braces
                                             Implicit -> Pretty.brackets
                                        ) $ pPrintPrec lvl prec $ snd hd
                                       )
                  ) empty args
    pPrintPrec lvl prec (PAlias _ name underp _) = text name <> text "@" <> Pretty.parens (pPrintPrec lvl prec underp)


-- False Left, True right
needParens :: Rational -> Term -> Bool
needParens r te = 
    let (prec, assoc) = decomposeRational r in
    let precte = termPrec te in
    let assocte = termAssoc te in
    if (precte < prec || (precte == prec && assocte == OpAssocRight)) then True else False

lowPrec :: Rational
lowPrec = (-1000) % 3557

instance Pretty Term where
    pPrintPrec lvl@(PrettyLevel i) prec te@(Type pos _) = 
        (if needParens prec te then Pretty.parens else id)
        (text "Type" <+> (if posShowLvl i then pPrintPrec lvl prec pos else empty))

    pPrintPrec lvl@(PrettyLevel i) prec  te@(Var pos name debruijn ty) = 
        (if needParens prec te then Pretty.parens else id)
        (text name <+> (if typeShowLvl i then pPrintPrec lvl prec ty else empty) <> (if posShowLvl i then pPrintPrec lvl prec pos else empty))

    pPrintPrec lvl@(PrettyLevel i) prec  te@(AVar pos _ ty) = 
        (if needParens prec te then Pretty.parens else id)
        (text "_" <+> (if typeShowLvl i then pPrintPrec lvl prec ty else empty) <+> (if posShowLvl i then pPrintPrec lvl prec pos else empty))

    pPrintPrec lvl@(PrettyLevel i) prec  te@(Lambda quants body pos ty) = 
        (if needParens prec te then Pretty.parens else id)
        (fsep [
            text "\\" <+> foldl (\ acc hd -> acc <+> pPrintPrec lvl prec hd) empty quants <+> text "->", 
            nest 2 $ pPrintPrec lvl lowPrec body, 
            (if typeShowLvl i then pPrintPrec lvl prec ty else empty), 
            (if posShowLvl i then pPrintPrec lvl prec pos else empty)
            ]
        )

    pPrintPrec lvl@(PrettyLevel i) prec  te@(Forall quants body pos ty) = 
        (if needParens prec te then Pretty.parens else id)
        (fsep [
            text "V" <+> foldl (\ acc hd -> acc <+> pPrintPrec lvl lowPrec hd) empty quants <+> text "->", 
            nest 2 $ pPrintPrec lvl prec body, 
            (if typeShowLvl i then pPrintPrec lvl prec ty else empty),
            (if posShowLvl i then pPrintPrec lvl prec pos else empty)
            ])

    pPrintPrec lvl@(PrettyLevel i) prec te@(Let [(var, def)] body pos ty) = 
        (if needParens prec te then Pretty.parens else id)
        (fsep [
            text "let" <+> text var <+> text "=" <+> pPrintPrec lvl lowPrec def <+> text "in", 
            nest 2 $ pPrintPrec lvl lowPrec body, 
            (if typeShowLvl i then pPrintPrec lvl prec ty else empty),
            (if posShowLvl i then pPrintPrec lvl prec pos else empty)
            ])
 
    pPrintPrec lvl@(PrettyLevel i) prec te@(App op@(Operator (OpInfix assoc opprec) s pos1 ty1 _) args pos2 ty2) | args' <- filter (\ (nat, _) -> nat == Explicite) args, length args' == 2 =        
        (if needParens prec te then Pretty.parens else id)
        (hsep [pPrintPrec lvl (termRationalPrec te) $ snd (args'!!0), text s, pPrintPrec lvl (termRationalPrec te) $ snd (args'!!1)])

    pPrintPrec lvl@(PrettyLevel i) prec te@(App op@(Operator (OpPrefix opprec) s pos1 ty1 _) args pos2 ty2) | args' <- filter (\ (nat, _) -> nat == Explicite) args, length args' == 1 =        
        (if needParens prec te then Pretty.parens else id)
        (hsep [text s, pPrintPrec lvl (termRationalPrec te) $ snd (args'!!0)])

    pPrintPrec lvl@(PrettyLevel i) prec te@(App op@(Operator (OpPostfix opprec) s pos1 ty1 _) args pos2 ty2) | args' <- filter (\ (nat, _) -> nat == Explicite) args, length args' == 1 =        
        (if needParens prec te then Pretty.parens else id)
        (hsep [pPrintPrec lvl (termRationalPrec te) $ snd (args'!!0), text s])
 
    
    pPrintPrec lvl@(PrettyLevel i) prec (te@(Operator o s pos ty _)) =
        Pretty.parens $ text s

    pPrintPrec lvl@(PrettyLevel i) prec (te@(DoNotation stmts pos ty)) =
        (if needParens prec te then Pretty.parens else id) $ (text "do {" $+$ 
                                                              (nest 4 $ foldl ($+$) empty $ map (\ stmt -> 
                                                                                                 case stmt of 
                                                                                                     DoLet n pos ty te -> text ";" <+> text n <+> text "=" <+> pPrintPrec lvl lowPrec te
                                                                                                     DoBind n pos ty te -> text ";" <+> text n <+> text "<-" <+> pPrintPrec lvl lowPrec te
                                                                                                     DoVal te pos ty -> text ";" <+> pPrintPrec lvl lowPrec te
                                                                                                 ) stmts)
                                                              $+$ text "}"
                                                             )



    pPrintPrec lvl@(PrettyLevel i) prec te@(App fct args pos ty) =
        (if needParens prec te then Pretty.parens else id)
        (hsep [
            pPrintPrec lvl prec fct,
            nest 2 $ hsep $ map (\ hd -> ((case fst hd of
                                               Explicite -> (if (needParens (termRationalPrec te) $ snd hd) then Pretty.parens else id) $ pPrintPrec lvl lowPrec $ snd hd
                                               Hidden -> if impliciteShowLvl i then Pretty.braces $ pPrintPrec lvl lowPrec $ snd hd else empty
                                               Implicit -> if oracledShowLvl i then Pretty.brackets $ pPrintPrec lvl lowPrec $ snd hd else empty
                                          ) 
                                         )
                                ) args,
            (if typeShowLvl i then pPrintPrec lvl prec ty else empty),
            (if posShowLvl i then pPrintPrec lvl prec pos else empty)
            ])

    pPrintPrec lvl@(PrettyLevel i) prec te@(Case fct cases pos ty) =
        (if needParens prec te then Pretty.parens else id)
        (fsep [text "case" <+> pPrintPrec lvl lowPrec fct <+> text "of", 
              foldl (\ acc (cases, def) -> 
                     acc $+$ foldl ( \ acc (pat, guards, _) -> acc $+$ fsep [nest 2 $ text "|" <+> pPrintPrec lvl lowPrec pat <+> foldl (\ acc (g, _, _) -> acc $+$ text "where" <+> pPrintPrec lvl lowPrec g) empty guards <+> text "=>"]) empty cases <+> pPrintPrec lvl lowPrec def
                    ) empty cases,
              (if typeShowLvl i then pPrintPrec lvl prec ty else empty), 
              (if posShowLvl i then pPrintPrec lvl prec pos else empty)
             ])

instance Pretty Definition where
    pPrintPrec lvl@(PrettyLevel i) prec te@(DefSig id pos ty) = 
        text "def" <+> text id <+> pPrintPrec lvl prec ty
