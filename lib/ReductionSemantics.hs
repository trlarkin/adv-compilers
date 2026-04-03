-- {-# LANGUAGE TupleSections #-}
module ReductionSemantics where

import           AbstractSyntax    as S
import           Data.Maybe
import qualified EvaluationContext as E
-- import           Latex
-- import           System.IO.Unsafe
import           Utils             as U

makeEvalContext :: S.Term -> Maybe (S.Term, E.Context)
makeEvalContext t = do
  case t of
    S.App (S.Abs _ _ _) t2
        -- v1 v2 -> (v1 v2, □)
        | S.isValue t2 -> Just (t, E.Hole)
    S.App t1 t2
        -- v1 t2 -> (t2, v1 □)
        | S.isValue t1 -> do (t2', c2) <- makeEvalContext t2; return (t2', E.AppV t1 c2)
        -- t1 t2 -> (t1, □ t2)
        | otherwise -> do (t1', c1) <- makeEvalContext t1; return (t1', E.AppT c1 t2)
    S.PrimApp p ts -> case span S.isValue ts of
        (_, []) -> return (t, E.Hole)
        (evaluated, rN:rest) -> do (tN', cN) <- makeEvalContext rN; return (tN', E.PrimApp p evaluated cN rest)
    S.If t1 t2 t3
        -- if True then t2 else t3 -> (t2, □)
        | S.Const S.Tru <- t1 -> return (t, E.Hole)
        -- if False then t2 else t3 -> (t3, □)
        | S.Const S.Fls <- t1 -> return (t, E.Hole)
        -- if t1 then t2 else t3 -> (t1, if □ then t2 else t3)
        | S.isNotValue t1 -> do (t1', c1) <- makeEvalContext t1; return (t1', E.If c1 t2 t3)
    S.Fix t1
        -- fix (λx.t11) -> ([x ↦ fix (λx.t11)] t11, □)
        | S.Abs _ _ _ <- t1 -> return (t, E.Hole) -- not correct TODO
        -- fix t1 -> (t1, fix □)
        | S.isNotValue t1 -> do (t1', c1) <- makeEvalContext t1; return (t1', E.Fix c1)
    S.Let x t1 t2
        -- let x = t1 in t2 -> (t1, let x = □ in t2) equivalent to (λx.t2) t1
        | S.isNotValue t1 -> do (t1', c1) <- makeEvalContext t1; return (t1', E.Let1 x c1 t2)
        -- let x = v1 in t2 -> ([x ↦ v1] t2, □)
        | otherwise -> return (t, E.Hole)
    S.Record labelsAndTerms -> case span (S.isValue . snd) labelsAndTerms of
        (_, []) -> return (t, E.Hole)
        (evaluated, (lN, tN):rest) -> do (tN', cN) <- makeEvalContext tN; return (tN', E.Record evaluated (lN, cN) rest)
    S.Project t1 l
        -- project t1.l -> (t1, project □.l)
        | S.isNotValue t1 -> do (t1', c1) <- makeEvalContext t1; return (t1', E.Project c1 l)
        -- project (record (... l=v ...)).l -> (v, □)
        | S.Record _ <- t1 -> return (t, E.Hole)
    S.Tag l1 t1 tau1
        -- tag (l = t1 as Varient(... l:T1 ...))
        | S.isNotValue t1 -> do (t1', c1) <- makeEvalContext t1; return (t1', E.Tag l1 c1 tau1)
    S.Case t1 lvt
        | S.isNotValue t1 -> do (t1', c1) <- makeEvalContext t1; return (t1', E.Case1 c1 lvt)
        | S.Tag {} <- t1 -> return (t, E.Hole)
    S.ErrorTerm err -> undefined `U.debug` show t
    v | S.isValue v -> Nothing
    _ -> error $ "not supported pattern: " ++ show t

makeContractum :: S.Term -> S.Term
makeContractum t = case t of
  S.App (S.Abs x _ t12) t2   ->  (x |-> t2) t12
--   S.Abs {}                     -> undefined
  S.PrimApp op ts                -> S.primOpEval op ts
--   S.If {}                      -> undefined
-- fix (λx.t11) -> ([x ↦ fix (λx.t11)] t11, □)
  S.If (S.Const pred') t2 t3
    | S.Tru <- pred' -> t2
    | S.Fls <- pred' -> t3
  S.Fix (S.Abs x _ t11)       -> (x |-> t) t11
--   S.Var {}                     -> undefined
--   S.Closure {}                 -> undefined
  S.Let x t1 t2                  -> (x |-> t1) t2
--   S.Const {}                 -> undefined
--   S.Record lts                  -> undefined
  S.Project (S.Record lts) l     -> fromJust $ lookup l lts
--   S.Tag l1 t1 tau1             -> undefined
  S.Case (S.Tag l1 t1 _) lxts -> fromJust $ do
    let (ls, xs, ts) = unzip3 lxts
    xBody <- lookup l1 (zip ls xs)
    tBody <- lookup l1 (zip ls ts)
    return $ (xBody |-> t1) tBody
  S.Fold {}                      -> undefined
  S.Unfold {}                    -> undefined
  S.ErrorTerm {}                 -> undefined
  _                              -> error $ "makeContractum: not a redex: " ++ show t

textualMachineStep :: S.Term -> Maybe S.Term
textualMachineStep t = do
    (t1, c) <- makeEvalContext t
    return $ E.fillWithTerm c (makeContractum t1)

textualMachineEval :: S.Term -> S.Term
textualMachineEval t =
  maybe t textualMachineEval (textualMachineStep t)

textualMachineTrace :: S.Term -> [S.Term]
textualMachineTrace t =
  case textualMachineStep t of
    Just t' -> t:textualMachineTrace t'
    Nothing -> []


