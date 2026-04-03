module StructuralOperationalSemantics_CBV_forDeBruijn where

-- import           Data.List
-- import           Data.Maybe
import           DeBruijnWithIntegerLabelsAndTags as S
import           Utils                            as U

replaceInFrame :: S.Term -> S.Term -> S.Term
replaceInFrame tBody v2 = S.shift 0 (-1) ((0 |-> S.shift 0 1 v2) tBody)

eval1 :: S.Term -> Maybe S.Term
eval1 t = case t of
    -- cant evaluate a value any further
    v | S.isValue v -> return v
    -- pg 103: E-AppAbs = (\x.t11) t2 -->
    S.App (S.Abs _ t12) v2
        | S.isValue v2 -> return $ replaceInFrame t12 v2
    -- pg 103: E-App2
    S.App v1 t2 | S.isValue v1 -> do t2' <- eval1 t2; return (S.App v1 t2')
    -- pg 103: E-App1
    S.App t1 t2 -> do t1' <- eval1 t1; return (S.App t1' t2)
    -- pg 144: E-FixBeta = fix (\x.t) --> [x |-> fix (\x.t)] t
    S.Fix (S.Abs _ t2) -> return $ replaceInFrame t2 t
    -- pg 144: E-Fix
    S.Fix t1 -> do t1' <- eval1 t1; return $ S.Fix t1'
    -- pg 124: E-LetV
    S.Let v1 t2 | S.isValue v1 -> return $ replaceInFrame t2 v1
    -- pg 124: E-Let
    S.Let t1 t2 -> do t1' <- eval1 t1; return $ S.Let t1' t2
    -- pg 34: E-IfTrue
    S.If (S.Const S.Tru) t2 _ -> return t2
    -- pg 34: E-IfFalse
    S.If (S.Const S.Fls) _ t3 -> return t3
    -- pg 34: E-If
    S.If t1 t2 t3 -> do t1' <- eval1 t1; return $ S.If t1' t2 t3
    -- primops
    S.PrimApp op xs
        | all S.isValue xs -> return (S.primOpEval op xs)
        | otherwise          -> do xs' <- mapM eval1 xs; return $ S.PrimApp op xs'
    -- pg 129: E-ProjRcd
    S.Project t1@(S.Record ts) i1 _
        | isValue t1 -> return $ ts!!i1
    -- pg 129:E-Prog
    S.Project t1 i1 i2 -> do t1' <- eval1 t1; return $ S.Project t1' i1 i2
    -- pg 129: E-Rcd
    S.Record ts -> do
        let vs = takeWhile S.isValue ts
        let (tN:rest) = dropWhile S.isValue ts
        tN' <- eval1 tN
        return $ Record (vs ++ [tN'] ++ rest)
    -- pg 136: E-Case-Variant
    S.Case (S.Tag i11 v11 _) _ its
        | S.isValue v11 -> do
            tBody <- lookup i11 its
            return $ replaceInFrame tBody v11
    -- pg 136; E-Case
    S.Case t1 tau1 its -> do t1' <- eval1 t1; return $ S.Case t1' tau1 its
    -- pg 136 E-Variant
    S.Tag i1 t1 tau1 -> do t1' <- eval1 t1; return $ S.Tag i1 t1' tau1
    _ -> error $ "unsupported DB term: " ++ show t


eval :: S.Term -> S.Term
eval v | S.isValue v = v
eval t =
    case eval1 t of
      Just t' -> eval t' --`U.debug` show t'
      Nothing -> t


