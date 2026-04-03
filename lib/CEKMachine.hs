module CEKMachine where

import Latex
import qualified AbstractSyntax as S

newtype Environment = Env [(S.Var, Closure)]
                      deriving Show

instance LatexShow Environment where
 latexShow (Env vcs) = "$\\{$" ++ foldr (\(x,c) -> \s -> x ++ "$\\mapsto$" ++ "*" ++ s) "$\\}$" vcs

newtype Closure = Clo (S.Term, Environment)
                  deriving Show

instance LatexShow Closure where
  latexShow (Clo (t, e)) = "$\\langle$" ++ latexShow t ++ ", " ++ latexShow e ++ "$\\rangle$"

isValueClosure :: Closure -> Bool
isValueClosure (Clo (t, _)) = S.isValue t

domainEnv :: Environment -> [S.Var]
domainEnv (Env vcs) = fst (unzip vcs)

emptyEnv :: Environment
emptyEnv = Env []

lookupEnv :: Environment -> S.Var -> Closure
lookupEnv (e@(Env [])) x  =  error ("variable " ++ x ++ " not bound in environment " ++ show e)
lookupEnv (Env ((v,c):t)) x
  | x == v     =  c
  | otherwise  =  lookupEnv (Env t) x

updateEnv :: Environment -> S.Var -> Closure -> Environment
updateEnv (Env vcs) x c = Env ((x,c):filter (\(v,_) -> v /= x) vcs)

data Cont  =  MachineTerminate
           |  Fun                Closure Cont -- where Closure is a value
           |  Arg                Closure Cont
           |  If                 Closure Closure Cont -- lazy 
           |  Fix                Cont
           |  PrimApp            S.PrimOp [Closure] [Closure] Cont -- where the first [Closure] contains values
           deriving Show

instance LatexShow Cont where
  latexShow  MachineTerminate            =  "$\\varodot$"
  latexShow  (Fun c kappa)           =  "$\\langle$fun " ++ latexShow c ++ " " ++ latexShow kappa ++ "$\\rangle$"
  latexShow  (Arg c kappa)           =  "$\\langle$arg " ++ latexShow c ++ " " ++ latexShow kappa ++ "$\\rangle$"
  latexShow  (If c1 c2 kappa)     =  "$\\langle$if " ++ latexShow c1 ++ " " ++ latexShow c2
                                               ++  " " ++ latexShow kappa ++ "$\\rangle$"
  latexShow  (Fix kappa)          =  "$\\langle$fix " ++ latexShow kappa ++ "$\\rangle$"

cekMachineStep :: (Closure, Cont) -> Maybe (Closure, Cont)
-- [cek3] and [cek4] should be at bottom due to the value match
cekMachineStep s = case s of
  {- Flatt & Felleisen Pg. 78 [cek1] -}
  (Clo (S.App t1 t2, e), kappa)               ->  Just (clos, cont)
    where cont = Arg (Clo (t2, e)) kappa
          clos = Clo (t1, e)
  {- Flatt & Felleisen Pg. 78 [cek2] -}
  (Clo (S.PrimOp op (t:ts), e), kappa)        -> Just (clos, cont)
    where clos = Clo (t,e)
          cont = PrimApp op [] (fmap Clo $ zip ts (repeat e)) kappa
  {- Flatt & Fellesin Pg. 78 [cek3] -}
  (c@(Clo (_, e)), Fun (Clo (S.Abs (S.Var x) _ t , e_prime)) kappa) -> if (isValueClosure c) then Just (clos, kappa) else Nothing
    where clos = Clo (t, updateEnv e_prime x c)
  {- Flatt & Felleisen Pg. 78 [cek4] -}
  (c@(Clo (_, e), Arg c2 kappa)) -> if (isValueClosure c) then Just (c2, Fun c kappa)
  {- Flatt & Felleisen Pg. 78 [cek5] -}
  ((Clo t@(S.Const b, e)), PrimApp op xs [] kappa) -> Just (clos, kappa)
    where clos = Clo (primOpEval op xs, emptyEnv)
  {- Flatt & Felleisen Pg. 78 [cek6] -}
  (c@(Clo (t, e)), PrimApp op xs (y:ys) kappa) -> if (isValueClosure c) then Just (y, PrimApp op (xs ++ [c]) ys kappa) else Nothing
  {- Flatt & Felleisen Pg. 78 [cek7] -}
  (Clo (S.Var v, e), kappa) -> Just (lookupEnv v e, kappa)
  _ -> Nothing

  
cekMachineLoop :: (Closure, Cont) -> Maybe (Closure, Cont)
cekMachineLoop ck =
  case cekMachineStep ck of
    Just ck' -> cekMachineLoop ck'
    Nothing -> Just ck

cekMachineTrace :: (Closure, Cont) -> [(Closure, Cont)]
cekMachineTrace ck =
    case cekMachineStep ck of
    Just ck' -> ck:cekMachineTrace ck'
    Nothing -> []

cekMachineTraceWithLast :: (Closure, Cont) -> [(Closure, Cont)]
cekMachineTraceWithLast ck =
    case cekMachineStep ck of
    Just ck' -> ck:cekMachineTraceWithLast ck'
    Nothing -> [ck]

cekMachineEval :: S.Term -> S.Term
cekMachineEval t =
  case cekMachineLoop (Clo (t, emptyEnv), MachineTerminate) of
    Just (Clo (v,_), MachineTerminate)
      | S.isValue v -> v
      | otherwise -> error "cekMachineEval: not value at end"
    Just (_, _) -> error "cekMachineEval: not MachineTerminate at end"
    Nothing -> error "cekMachineEval: not possible"

cekMachineLatexDisplayState :: (Closure, Cont) -> String
cekMachineLatexDisplayState (c, kappa) = "$\\langle$" ++ latexShow c ++ ", \\textcolor{red}{"
                                        ++ latexShow kappa ++ "}$\\rangle$"

cekMachineLatexDisplayEvaluation :: S.Term -> String
cekMachineLatexDisplayEvaluation t =
  foldr  (\ck -> \s -> cekMachineLatexDisplayState ck ++ "\\\\\n" ++ s)
         ""
         trace
  where
    trace = cekMachineTraceWithLast (Clo (t, emptyEnv), MachineTerminate)