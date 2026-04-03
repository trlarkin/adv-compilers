\newpage
\section{Natural Semantics With Environments, Closures, and Nameless Terms Using de Bruijn Indices}


\begin{code}
module NaturalSemanticsWithEnvironmentsClosuresAndDeBruijnIndices_CBV where

import Data.Maybe
import qualified DeBruijnWithIntegerLabelsAndTags as S
import qualified IntegerArithmetic as I

data Value = Clo S.Term Env
           | BoolVal Bool
           | IntVal I.IntegerType
           | CharVal Char
           | UnitVal
           | RecordVal [Value]
           | TagVal Int Value
           | FoldVal Value
           deriving Show

type Env = [Value]

evalInEnv :: Env -> S.Term -> Maybe Value
evalInEnv e t = case t of
  S.Var i         ->  Just (e!!i)
  S.Abs tau t1    ->  Just (Clo (S.Abs tau t1) e)
  S.App t1 t2     ->  do
                        Clo (S.Abs tau t') e' <- evalInEnv e t1
                        v' <- evalInEnv e t2
                        evalInEnv (v':e') t'
  ...
  
constEval :: S.Const -> Value
constEval c = case c of
  S.Tru          ->  BoolVal True
  S.Fls          ->  BoolVal False
  S.IntConst i   ->  IntVal i
  S.CharConst c  ->  CharVal c
  S.Unit         ->  UnitVal

constUneval :: Value -> S.Const
constUneval c = case c of
  BoolVal True   ->  S.Tru
  BoolVal False  ->  S.Fls
  IntVal i       ->  S.IntConst i
  CharVal c      ->  S.CharConst c
  UnitVal        ->  S.Unit

primOpEval :: S.PrimOp -> [Value] -> Value
primOpEval p vs = let S.Const c = S.primOpEval p (map (S.Const . constUneval) vs)
                  in constEval c

eval :: S.Term -> Value
eval t = fromJust (evalInEnv [] t)
\end{code}



