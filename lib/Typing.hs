{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use tuple-section" #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
module Typing where

import           AbstractSyntax as S hiding (Bind, Empty)
import           Control.Monad
import           Data.List
import           ErrorMessages  as ErrMsg
import           Utils          as U

data Context = Empty | Bind Context (S.Var, S.Type) deriving (Eq)

instance Show Context where
    show Empty = "<>"
    show (Bind gamma (x, tau)) = show gamma ++ "," ++ show x ++ "," ++ ":" ++ show tau

-- -- | builds a type binding tuple
-- (#:) :: Var -> Type -> (Var, Type)
-- x #: tau = (x, tau)
-- infixl 2 #:

contextLookup :: S.Var -> Context -> Either String S.Type
contextLookup x Empty = Left ("\"" ++ x ++ "\" is a free variable and cannot be type checked.")
contextLookup x (gamma `Bind` (y, tau))
        | x == y = Right tau
        | otherwise = contextLookup x gamma

-- | Alias for typing that more closely matches the notation in TAPL
(|-) :: Context -> Term -> Either String Type
(|-) = typing

-- TODO: add references to TAPL to make sure these are all correct
typing :: Context -> S.Term -> Either String S.Type
typing gamma t = case t of
    S.ErrorTerm s -> Left s -- term that represents a runtime error
    S.Var x -> contextLookup x gamma -- pg 103: T-Var
    S.Abs x tau1 t2 -> do -- pg 103: T-Abs
        tau2 <- gamma `Bind` (x, tau1) |- t2
        Right (S.TypeArrow tau1 tau2)
    S.App t1 t2 -> do -- pg 103: T-App
        tau1 <- gamma |- t1
        case tau1 of
            S.TypeArrow tauFrom tauTo -> enforceType t2 tauFrom gamma >> return tauTo
            _ -> Left (show t1 ++ " is not an arrow type")
    S.Let x t1 t2 -> do
        tau1 <- typing gamma t1
        tau2 <- typing (gamma `Bind` (x, tau1)) t2
        Right tau2
    S.Const c -> return $ constType c -- constant typing
    S.If t1 t2 t3 -> do -- pg 93: T-If
        enforceType t1 S.TypeBool gamma
        tau2 <- typing gamma t2
        tau3 <- typing gamma t3
        if tau2 == tau3
            then Right tau2
            else Left $ ErrMsg.ifMismatch (t2, tau2, t3, tau3, t)
    S.PrimApp op args -> do --
        let (tauArgs, tau) = S.primOpType op
        zipWithM_ (\t' tau' -> enforceType t' tau' gamma) args tauArgs
        return tau
    -- pg 144: T-Fix    if (gamma |- t1 !: T1->T1)   ->(->(Int, C),->(Int, (Unit|N)))
    S.Fix t1 -> case typing gamma t1 of              -- =(Int-> (N -m> (Unit|N))->(Int -> (Unit|N))
        Right (S.TypeArrow x y)                  -- =Int-> N -> (Int -> (Unit|N))   C n = Z Unit | S n
            | x == y -> return x
        _ -> do
            tau1 <- typing gamma t1
            Left $ ErrMsg.fixErr (tau1, t)
    -- S.Fix t1
    --     | (S.Abs x tauX tBody) <- t1 -> do
    --         let gamma' = gamma `Bind` (x, tauX)
    --         enforceType tBody tauX gamma'
    --     | otherwise -> do
    --         tau1 <- typing gamma t1
    --         Left $ ErrMsg.fixErr (tau1, t)
    S.Record labelsAndTerms -> do
        let (labels, terms) = unzip labelsAndTerms
        types <- mapM (typing gamma) terms
        return $ S.TypeRecord $ zip labels types
    S.Project tOuter labelInner -> case typing gamma tOuter of
        Right (S.TypeRecord labelsAndTypes) -> do
            U.lookupOrElse labelInner labelsAndTypes ("the Label " ++ show labelInner ++ " is not a valid label in: " ++ show t)
        _ -> Left ("'" ++ show tOuter ++ "' is not a Record in project statement: \"" ++ show t ++ "\"")
    S.Tag tagLabel t1 tau -> case tau of
        S.TypeVariant labelsAndTypes -> do
            tau1 <- U.lookupOrElse tagLabel labelsAndTypes ("the Label " ++ show tagLabel ++ " is not a valid " ++ show tau ++ " in " ++ show t)
            enforceType t1 tau1 gamma
            return tau
        _ -> Left ("'" ++ show tau ++ "' is not a Variant in tag statement: \"" ++ show t ++ "\"")
    S.Case t1 lvt -> case typing gamma t1 of -- needs more checks
        Right tau1@(S.TypeVariant labelsAndTypes) -> do
            -- if sort labelsBody == sort labelsFocus
            if all (`elem` labelsFocus) labelsBody
                then isSameType
                else Left (show tau1 ++ " do not have the same labels as " ++ show t)
            where
                (labelsBody, vars, terms) = unzip3 lvt
                (labelsFocus, _) = unzip labelsAndTypes
                helper :: S.Label -> S.Var -> S.Term -> Either String S.Type
                helper lA varA tB = do
                    tauA <- U.lookupOrElse lA labelsAndTypes ("label \'" ++ lA ++ "\' is not valid for " ++ show tau1 ++ " in: " ++ show t)
                    let gamma' = gamma `Bind` (varA,  tauA)
                    typing gamma' tB
                typesBody = sequence $ zipWith3 helper labelsBody vars terms
                allSameType :: [S.Type] -> Either String S.Type
                allSameType [] = Left "Must have at least one element in list"
                allSameType [x] = Right x
                allSameType (x:y:ys)
                    | x == y = allSameType (y:ys)
                    | otherwise = Left ("all paths must return the same type in the case statement: " ++ show t)
                isSameType = allSameType =<< typesBody
        Left x -> Left x
        Right tauNotVariant -> Left $ ErrMsg.notVariantInCase (t1, t)
    S.Fold u t1 -- pg 276: T-Fld
        | S.TypeMu chi tau1 <- u -> enforceType t1 ((chi |-> u) tau1) gamma >> return u
        | otherwise -> Left $ "folding without mu operator in " ++ show t
    S.Unfold u t1 -- pg 276: T-Unfld
        | S.TypeMu chi tau1 <- u -> enforceType t1 u gamma >> return ((chi |-> u) tau1)
        | otherwise -> Left $ "folding without a mu operator in " ++ show t
    S.Closure _ _ -> undefined
    -- tUnknown -> Left ("typing for " ++ show tUnknown ++ " is not implemented")
    where
        enforceType :: Term -> Type -> Context -> Either String Type
        enforceType tGiven tauExpected gamma' = do
            tauGiven <- typing gamma' tGiven
            if tauExpected == tauGiven
                then Right tauExpected
                else Left $ ErrMsg.wrongType (tGiven, tauGiven, tauExpected, t)

        -- | Enforce the type of the term on the left is the type given on the right.
        -- | If the type is not correct then return the standard wrongType error message.
        (!:) :: Term -> Type -> Context -> Either String Type
        (!:) = enforceType


typeCheck :: S.Term -> S.Type
typeCheck t =
    case typing Empty t of
        Right tau   -> tau
        Left errMsg -> S.TypeError errMsg

