module CKMachine where

import           AbstractSyntax as S
import           Latex

data Cont  =  KMachineTerminate
           |  KFun              S.Term Cont -- where Term is a value
           |  KArg              S.Term Cont
           |  KIf               S.Term S.Term Cont
           |  KPrimApp          S.PrimOp [S.Term] [S.Term] Cont -- where the first [S.Term] contains values
           |  KFix              Cont
           |  KLet              String S.Term Cont
           deriving Show

instance LatexShow Cont where
  latexShow  KMachineTerminate            =  "$\\varodot$"
  latexShow  (KArg t kappa)               =  "$\\langle$arg " ++ latexShow t ++ " " ++ latexShow kappa ++ "$\\rangle$"
  latexShow  (KFun t kappa)               =  "$\\langle$fun " ++ latexShow t ++ " " ++ latexShow kappa ++ "$\\rangle$"
  latexShow  (KIf t1 t2 kappa)            =  "$\\langle$if " ++ latexShow t1 ++ " " ++ latexShow t2
                                            ++  " " ++ latexShow kappa ++ "$\\rangle$"
  latexShow  (KFix kappa)                 =  "$\\langle$fix " ++ latexShow kappa ++ "$\\rangle$"

ckMachineStep :: (S.Term, Cont) -> Maybe (S.Term, Cont)
ckMachineStep s = case s of -- L&L pg. 72
    (v, KMachineTerminate) | S.isValue v            -> Nothing
    (S.App m n, kappa)                              -> return (m, KArg n kappa) -- ck1
    (S.PrimApp p (m:ts), kappa)                     -> return (m, KPrimApp p [] ts kappa) -- ck2
    (v, KFun (S.Abs x _ m) kappa) | S.isValue v     -> return ((x |-> v) m, kappa) -- ck3
    (v, KArg n kappa) | S.isValue v                 -> return (n, KFun v kappa) -- ck4
    (b, KPrimApp p bs [] kappa) | S.isValue b       -> return (S.primOpEval p (reverse (b:bs)), kappa) -- ck5
    (v, KPrimApp p vs (n:ls) kappa) | S.isValue v   -> return (n, KPrimApp p (v:vs) ls kappa) -- ck6

    (S.If t1 t2 t3, kappa)                          -> return (t1, KIf t2 t3 kappa) -- ck make if
    (S.Const b, KIf t2 t3 kappa) -- ck eval if
        | S.Tru <- b                                -> return (t2, kappa)
        | S.Fls <- b                                -> return (t3, kappa)

    (S.Fix t1, kappa)                               -> return (t1, KFix kappa) -- ck make fix
    (v@(S.Abs x _ m), KFix kappa)                   -> return ((x |-> S.Fix v) m, kappa) -- ck eval fix

    (S.Let x t1 t2, kappa)                          -> return (t1, KLet x t2 kappa) -- ck make let
    (v, KLet x t2 kappa) | S.isValue v              -> return ((x |-> v) t2, kappa) -- ck eval let

    _                                               -> error ("unsupported CK step: " ++ show s)

ckMachineLoop :: (S.Term, Cont) -> Maybe (S.Term, Cont)
ckMachineLoop tc =
  case ckMachineStep tc of
    Just tc' -> ckMachineLoop tc'
    Nothing  -> Just tc

ckMachineTrace :: (S.Term, Cont) -> [(S.Term, Cont)]
ckMachineTrace tc =
    case ckMachineStep tc of
    Just tc' -> tc:ckMachineTrace tc'
    Nothing  -> []

ckMachineTraceWithLast :: (S.Term, Cont) -> [(S.Term, Cont)]
ckMachineTraceWithLast tc =
    case ckMachineStep tc of
    Just tc' -> tc:ckMachineTraceWithLast tc'
    Nothing  -> [tc]

ckMachineEval :: S.Term -> S.Term
ckMachineEval t =
  case ckMachineLoop (t, KMachineTerminate) of
    Just (v, KMachineTerminate)
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
    trace = ckMachineTraceWithLast (t, KMachineTerminate)


-- (IntMul[
--     3,
--     if IntEq(0, 2) then 1 else
--         IntMul(2, app(fix(abs(f: ->(Int,Int). abs(x: Int. if IntEq(0, x) then 1 else
--             IntMul(x, app(f, IntSub(x, 1))) fi))), IntSub(2, 1))) fi
-- ],
-- KFun abs(x: Int. if IntEq(0, x) then 1 else IntMul(x, app(fix(abs(f: ->(Int,Int). abs(x: Int. if IntEq(0, x) then 1 else IntMul(x, app(f, IntSub(x, 1))) fi))), IntSub(x, 1))) fi) KMachineTerminate)
