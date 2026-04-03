\newpage
\section{CC machine}

Towards more efficient machines: In the CC machine, the state is a pair (control string, context)

\begin{code}
module CCMachine where

import Latex
import qualified AbstractSyntax as S
import qualified EvaluationContext as E

ccMachineStep :: (S.Term, E.Context) -> Maybe (S.Term, E.Context)
ccMachineStep (t, c) = case t of
  S.App t1 t2
    | not (S.isValue t1)                      ->   Just (t1, E.fillWithContext c (E.AppT E.Hole t2))       {-cc1-}
    | S.isValue t1 && not (S.isValue t2)      ->   Just (t2, E.fillWithContext c (E.AppV t1 E.Hole))       {-cc2-}
  S.App (S.Abs x _ t12) t2                    ->   Just (S.subst x t2 t12, c)                              {-ccbeta-}
  ...
  S.PrimApp p ts                              ->   if null rest then Just (S.primOpEval p ts, c)           {-ccdelta-}
                                                   else Just (head rest, E.fillWithContext c (E.PrimApp p evaluated E.Hole (tail rest)))
                                                   where
                                                     (evaluated, rest) = span S.isValue ts
  ...
  v | S.isValue v                             ->   shift v c
  where
    shift :: S.Term -> E.Context -> Maybe (S.Term, E.Context)
    ...

ccMachineLoop :: (S.Term, E.Context) -> Maybe (S.Term, E.Context)
ccMachineLoop tc =
  case ccMachineStep tc of
    Just tc' -> ccMachineLoop tc'
    Nothing -> Just tc

ccMachineEval :: S.Term -> S.Term
ccMachineEval t =
  case ccMachineLoop (t, E.Hole) of
    Just (v, E.Hole)
      | S.isValue v -> v
      | otherwise -> error "ccMachineEval: not value at end"
    Just (_, _) -> error "ccMachineEval: not hole at end"
    Nothing -> error "ccMachineEval: not possible"

ccMachineTrace :: (S.Term, E.Context) -> [(S.Term, E.Context)]
ccMachineTrace tc =
    case ccMachineStep tc of
    Just tc' -> tc:ccMachineTrace tc'
    Nothing -> []

ccMachineTraceWithLast :: (S.Term, E.Context) -> [(S.Term, E.Context)]
ccMachineTraceWithLast tc =
    case ccMachineStep tc of
    Just tc' -> tc:ccMachineTraceWithLast tc'
    Nothing -> [tc]

ccMachineLatexDisplayState :: (S.Term, E.Context) -> String
ccMachineLatexDisplayState (t, e) = "$\\langle$" ++ latexShow t ++ ", \\textcolor{blue}{" ++ latexShow e ++ "}$\\rangle$"

ccMachineLatexDisplayEvaluation :: S.Term -> String
ccMachineLatexDisplayEvaluation t =
  foldr  (\te -> \s -> ccMachineLatexDisplayState te ++ "\\\\\n" ++ s)
         ""
         trace
  where
    trace = ccMachineTraceWithLast (t, E.Hole)
\end{code}

The function |shift| is complex because it must find the \emph{innermost} evaluation subcontext in
a context, and therefore can't use Haskell pattern matching.


