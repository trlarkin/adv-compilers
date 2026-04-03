\section{Natural Semantics With Environments And Closures}
Quite like the presentation in Gilles Kahn's 1987 paper:
Gilles Kahn. Natural semantics. [Research Report] RR-0601, INRIA. 1987.
\begin{code}
module NaturalSemanticsWithEnvironmentsAndClosures_CBV where

import Data.Maybe
import Data.List
import qualified AbstractSyntax as S
import qualified IntegerArithmetic as I

data Value = Clo S.Term Env
           | BoolVal Bool
           | IntVal I.IntegerType
           | CharVal Char
           | UnitVal
           | RecordVal [(S.Label,Value)]
           | TagVal S.Label Value
           | FoldVal Value
           deriving Show

type Env = [(S.Var, Value)]

evalInEnv :: Env -> S.Term -> Maybe Value
evalInEnv e t = case t of
  S.Var x         ->  lookup x e
  S.Abs x tau t1  ->  Just (Clo (S.Abs x tau t1) e)
  S.App t1 t2     ->  do
                        Clo (S.Abs x tau t') e' <- evalInEnv e t1
                        v' <- evalInEnv e t2
                        evalInEnv ((x,v'):e') t'
  ...
  ...
  ...
eval :: S.Term -> Value
eval t = fromJust (evalInEnv [] t)
\end{code}
