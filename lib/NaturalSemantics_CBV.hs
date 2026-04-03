


module NaturalSemantics_CBV where

import qualified AbstractSyntax as S
import           Data.List

eval :: S.Term -> Maybe S.Term
eval t = case t of
  v | S.isValue v  ->  return v
  S.App t1 t2      ->  do
                        S.Abs x _ t' <- eval t1
                        v2 <- eval t2
                        eval (S.subst x v2 t')
  S.PrimApp op ts -> S.primOpEval op <$> mapM eval ts
  S.If t1 t2 t3 -> do
                      S.Const b <- eval t1
                      if b == S.Tru
                        then eval t2
                        else eval t3
  S.Let x t1 t2 -> do
                      a <- eval t1 -- alpha
                      eval $ (x S.|-> a) t2 -- beta
  S.Fix t1 -> do -- adapted from letrec definition
                S.Abs x _ t' <- eval t1 -- fix (\x.t) -> [x |-> fix (\x.t)] t
                eval $ (x S.|-> t) t'
  _                ->  Nothing




