module EvaluationContext where

import qualified AbstractSyntax as S
import           Data.List
import           Latex

data Context  =  Hole
              |  AppT        Context S.Term
              |  AppV        S.Term Context -- where Term is a value
              |  If          Context S.Term S.Term
              |  Fix         Context
              |  PrimApp     S.PrimOp [S.Term] Context [S.Term] -- where Terms before the Context are values
              |  Let1        S.Var Context S.Term
              |  Record      [(S.Label, S.Term)] (S.Label, Context) [(S.Label, S.Term)]
              |  Project     Context S.Label
              |  Tag         S.Label Context S.Type
              |  Case1       Context [(S.Label, S.Var, S.Term)]
              deriving (Eq)

instance Show Context where
    show e = case e of
        Hole                            -> "□"
        AppT e t2                       -> "app(" ++ show e ++ ", " ++ show t2 ++ ")"
        AppV v1 e                       -> "app(" ++ show v1 ++ ", " ++ show e ++ ")"
        If e t2 t3                      -> "if " ++ show e ++ " then " ++ show t2 ++ " else " ++ show t3 ++ " fi "
        Fix e                           -> "fix (" ++ show e ++ ")"
        PrimApp op ts1 e ts2            -> show op ++ "("
                                            ++ intercalate ", " (map show ts1)
                                            ++ ", " ++  show e ++ ", "
                                            ++ intercalate ", " (map show ts2) ++ ")"
        Let1  x e t2                    -> "let " ++ x ++ " = " ++ show e ++ " in " ++ show t2 ++ " end"
        -- Let2  x t1 e                    -> "let " ++ x ++ " = " ++ show t1 ++ " in " ++ show e ++ " end"
        Record  lts1 (l, e) lts2        -> "record(" ++ "... " ++ l ++ "=" ++ show e ++ " ..." ++ ")"
        Project e l                     -> "project(" ++ show e ++ "." ++ l ++ ")"
        Tag l e tau                     -> "tag(" ++ l ++ " = " ++ show e ++ " as " ++ show tau ++ ")"
        Case1 e lxts                    -> "case " ++ show e ++ " of "
                                            ++ caseInter lxts
                                            ++ " esac"
        -- Case2  t1 lxts1 (l,x,e) lxvs2   -> "case " ++ show e ++ " of "
        --                                     ++ "... " -- caseInter lxts1
        --                                     ++ " | " ++ l ++ " = " ++ x ++ " => " ++ show e
        --                                     ++ " ..." -- caseInter lxvs2
        --                                     ++ " esac"
        where
            caseInter lxts = intercalate " | " (map (\(l,x,t'') -> l ++ " = " ++ x ++ " => " ++ show t'') lxts)

instance LatexShow Context where
    latexShow c = "unimplemented: latexShow for EvaluationContext.Context"

fillWithTerm :: Context -> S.Term -> S.Term
fillWithTerm e t = case e of
    Hole                                ->  t
    AppT e1 t2                          ->  S.App (fillWithTerm e1 t) t2
    AppV t1 e2                          ->  S.App t1 (fillWithTerm e2 t)
    If e1 t2 t3                         ->  S.If (fillWithTerm e1 t) t2 t3
    Fix e1                              ->  S.Fix (fillWithTerm e1 t)
    PrimApp p ts1 e1 ts2                ->  S.PrimApp p (ts1 ++ [fillWithTerm e1 t] ++ ts2)
    Let1 x e1 t2                        ->  S.Let x (fillWithTerm e1 t) t2
    -- Let2 x t1 e2                        ->  S.Let x t1 (fillWithTerm e2 t)
    Record qPre (l1, e1) qPost          ->  S.Record (qPre ++ [(l1, fillWithTerm e1 t)] ++ qPost)
    Project e1 l1                       ->  S.Project (e1 `fillWithTerm` t) l1
    Tag l1 e1 tau1                      ->  S.Tag l1 (e1 `fillWithTerm` t) tau1
    Case1 e1 q                          ->  S.Case (e1 `fillWithTerm` t) q
    -- Case2 t1 qPre (l2, x2, e2) qPost    ->  S.Case t1 (qPre ++ [(l2, x2, fillWithTerm e2 t)] ++ qPost)

fillWithContext :: Context -> Context -> Context
fillWithContext e e' = case e of
    Hole                       ->  e'
    AppT e1 t2                 ->  AppT (fillWithContext e1 e') t2
    AppV t1 e2                 ->  AppV t1 (fillWithContext e2 e')
    If e1 t2 t3                ->  If (fillWithContext e1 e') t2 t3
    Fix e1                     ->  Fix (fillWithContext e1 e')
    PrimApp p ts1 e1 ts2       ->  PrimApp p ts1 (fillWithContext e1 e') ts2
    Let1 x e1 t2               ->  Let1 x (fillWithContext e1 e') t2
    -- Let2 x t1 e2                        ->  Let2 x t1 (fillWithContext e2 e')
    Record qPre (l1, e1) qPost ->  Record qPre (l1, fillWithContext e1 e') qPost
    Project e1 l1              ->  Project (e1 `fillWithContext` e') l1
    Tag l1 e1 tau1             ->  Tag l1 (e1 `fillWithContext` e') tau1
    Case1 e1 q                 ->  Case1 (e1 `fillWithContext` e') q
    -- Case2 t1 qPre (l2, x2, e2) qPost    ->  Case2 t1 qPre (l2, x2, fillWithContext e2 e') qPost

