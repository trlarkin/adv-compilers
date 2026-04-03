\newpage
\section{CK machine}
Follows Felleisen and Flatt. We specialize the continuation constructors. Note our non-strict conditional.

\begin{code}
module CKMachine where

import Latex
import qualified AbstractSyntax as S

data Cont  =  MachineTerminate
           |  Fun              S.Term Cont -- where Term is a value
           |  Arg              S.Term Cont
           |  If               S.Term S.Term Cont
           |  PrimApp          S.PrimOp [S.Term] [S.Term] Cont -- where the first [S.Term] contains values
           |  Fix              Cont
           deriving Show

instance LatexShow Cont where
  latexShow  MachineTerminate            =  "$\\varodot$"
  latexShow  (Arg t kappa)               =  "$\\langle$arg " ++ latexShow t ++ " " ++ latexShow kappa ++ "$\\rangle$"
  latexShow  (Fun t kappa)               =  "$\\langle$fun " ++ latexShow t ++ " " ++ latexShow kappa ++ "$\\rangle$"
  latexShow  (If t1 t2 kappa)            =  "$\\langle$if " ++ latexShow t1 ++ " " ++ latexShow t2 
                                            ++  " " ++ latexShow kappa ++ "$\\rangle$"
  latexShow  (Fix kappa)                 =  "$\\langle$fix " ++ latexShow kappa ++ "$\\rangle$"

ckMachineStep :: (S.Term, Cont) -> Maybe (S.Term, Cont)
ckMachineStep s = case s of
  (S.App t1 t2, kappa)                 ->  Just (t1, Arg t2 kappa)                                {-ck1-}
  ...
  
ckMachineLoop :: (S.Term, Cont) -> Maybe (S.Term, Cont)
ckMachineLoop tc =
  case ckMachineStep tc of
    Just tc' -> ckMachineLoop tc'
    Nothing -> Just tc

ckMachineTrace :: (S.Term, Cont) -> [(S.Term, Cont)]
ckMachineTrace tc =
    case ckMachineStep tc of
    Just tc' -> tc:ckMachineTrace tc'
    Nothing -> []

ckMachineTraceWithLast :: (S.Term, Cont) -> [(S.Term, Cont)]
ckMachineTraceWithLast tc =
    case ckMachineStep tc of
    Just tc' -> tc:ckMachineTraceWithLast tc'
    Nothing -> [tc]

ckMachineEval :: S.Term -> S.Term
ckMachineEval t =
  case ckMachineLoop (t, MachineTerminate) of
    Just (v, MachineTerminate)
      | S.isValue v -> v
      | otherwise -> error "ckMachineEval: not value at end"
    Just (_, _) -> error "ckMachineEval: not MachineTerminate at end"
    Nothing -> error "ckMachineEval: not possible"

ckMachineLatexDisplayState :: (S.Term, Cont) -> String
ckMachineLatexDisplayState (t, kappa) = "$\\langle$" ++ latexShow t ++ ", \\textcolor{red}{"
                                        ++ latexShow kappa ++ "}$\\rangle$"

ckMachineLatexDisplayEvaluation :: S.Term -> String
ckMachineLatexDisplayEvaluation t =
  foldr  (\tc -> \s -> ckMachineLatexDisplayState tc ++ "\\\\\n" ++ s)
         ""
         trace
  where
    trace = ckMachineTraceWithLast (t, MachineTerminate)
\end{code}
