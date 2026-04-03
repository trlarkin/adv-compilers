
Plotkin-style structural operational semantics, call-by-value.
Inference rules are named as in TAPL. Here they
are implemented algorithmically.

The function |eval| captures the small-step evaluation relation for our
calculus.

\begin{code}
module StructuralOperationalSemantics_CBV_forDeBruijn where

import Data.Maybe
import Data.List
import qualified DeBruijnWithIntegerLabelsAndTags as S

eval1 :: S.Term -> Maybe S.Term
eval1 t = case t of
  S.App (S.Abs tau11 t12) t2
    |  S.isValue t2 -> Just (S.shift 0 (-1) (S.subst 0 (S.shift 0 1 t2) t12))
  S.App t1 t2
    |  S.isValue t1 -> do t2' <- eval1 t2; Just (S.App t1 t2')                              -- E-App2
    |  otherwise -> do t1' <-  eval1 t1; Just (S.App t1' t2)                                -- E-App1

eval :: S.Term -> S.Term
eval t =
  case eval1 t of
    Just t' -> eval t'
    Nothing -> t
\end{code}

