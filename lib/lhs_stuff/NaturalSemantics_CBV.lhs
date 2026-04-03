\section{Simple Natural Semantics, also known as Big-Step Operational Semantics}

\begin{code}
module NaturalSemantics_CBV where

import Data.List
import qualified AbstractSyntax as S

eval :: S.Term -> Maybe S.Term
eval t = case t of
  S.Abs x tau t1  ->  Just (S.Abs x tau t1)
  S.App t1 t2     ->  do
                        S.Abs x tau t' <- eval t1
                        v2 <- eval t2
                        eval (S.subst x v2 t')
  ...
  ...
  ...
  _               ->  Nothing
\end{code}



