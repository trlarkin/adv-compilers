\section{Evaluation Contexts for Reduction Semantics}

\begin{code}
module EvaluationContext where

import Latex
import qualified AbstractSyntax as S

data Context  =  Hole
              |  AppT        Context S.Term
              |  AppV        S.Term Context -- where Term is a value
              |  If          Context S.Term S.Term
              |  Fix         Context
              |  PrimApp     S.PrimOp [S.Term] Context [S.Term] -- where Terms before the Context are values
              ...
              deriving (Eq, Show)

instance LatexShow Context where
  latexShow c = "unimplemented: latexShow for EvaluationContext.Context"

fillWithTerm :: Context -> S.Term -> S.Term
fillWithTerm c t = case c of
  Hole                  ->  t
  AppT c1 t2            ->  S.App (fillWithTerm c1 t) t2
  AppV t1 c2            ->  S.App t1 (fillWithTerm c2 t)
  If c1 t2 t3           ->  S.If (fillWithTerm c1 t) t2 t3
  Fix c1                ->  S.Fix (fillWithTerm c1 t)
  PrimApp p ts1 c1 ts2  ->  S.PrimApp p (ts1 ++ [fillWithTerm c1 t] ++ ts2)
  ...

fillWithContext :: Context -> Context -> Context
fillWithContext c c' = case c of
  Hole                  ->  c'
  AppT c1 t2            ->  AppT (fillWithContext c1 c') t2
  AppV t1 c2            ->  AppV t1 (fillWithContext c2 c')
  If c1 t2 t3           ->  If (fillWithContext c1 c') t2 t3
  Fix c1                ->  Fix (fillWithContext c1 c')
  PrimApp p ts1 c1 ts2  ->  PrimApp p ts1 (fillWithContext c1 c') ts2
  ...
\end{code}
