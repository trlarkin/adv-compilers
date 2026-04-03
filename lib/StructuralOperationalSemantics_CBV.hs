{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module StructuralOperationalSemantics_CBV where

import           AbstractSyntax as S
import           Utils          as U
import           Debug.Trace    as D 

-- Big-step semantics
eval_big :: S.Term -> S.Environment -> Either String S.Term
eval_big t@(S.Const x) _ = Right t
eval_big t@(S.Record _) _ = Right t
eval_big (S.Var x) e = S.lookupEnv x e
eval_big t@(S.Abs _ _ _) e = Right (S.Closure t e)
eval_big t@(S.App t1 t2) e = case (eval_big t1 e) of
    Right (S.Closure (S.Abs x _ t12) e_prime) -> do
        v2 <- eval_big t2 e
        v <- eval_big t12 (S.Bind (x,v2) e_prime)
        return v
    err@(Left _) -> err
    _            -> Left ("Error evaluating " ++ (show t) ++ " with environment " ++ (show e))
eval_big t@(S.If t1 t2 t3) e = do
    v1 <- eval_big t1 e
    case v1 of
        (S.Const S.Tru) -> do v2 <- eval_big t2 e; return v2
        (S.Const S.Fls) -> do v3 <- eval_big t3 e; return v3
        _                 -> Left ("Error evaluating " ++ (show t) ++ " with env " ++ (show e))
eval_big t@(S.PrimApp op xs) e = do
    xs_val <- mapM ((flip $ eval_big) e) xs
    return (S.primOpEval op xs_val)
eval_big t e = Left ("Error evaluating term " ++ (show t) ++ " with environment " ++ (show e))



-- Small-step semantics
eval_small :: S.Term -> Either String S.Term
eval_small t -- return self
    | S.Const _  <- t = return t
    | S.Var _    <- t = return t
    | S.Abs {}   <- t = return t
eval_small t = case t of
-- error
    S.ErrorTerm err -> Left $ "something went wrong! term errored during small step evaluation: " ++ err
-- pg 103: E-AppAbs
    S.App t1@(S.Abs x _ t12) v2 
      | S.isValue v2 -> return $ (x |-> v2) t12
      | otherwise    -> do t1' <- eval_small v2; return $ S.App t1 t1'
-- pg 103: E-App2
    S.App v1 t2 | S.isValue v1 -> do t2' <- eval_small t2; return $ S.App v1 t2'
-- pg 103: E-App1
    S.App t1 t2 -> do t1' <-  eval_small t1; return $ S.App t1' t2
-- pg 144: E-FixBeta
    S.Fix f@(S.Abs x _ t2) -> return $ (x |-> S.Fix f) t2
-- pg 144: E-Fix
    S.Fix t1 -> do t1' <- eval_small t1; return $ S.Fix t1'
-- pg 124: E-LetV
    S.Let x v1 t2 | S.isValue v1 -> return $ (x |-> v1) t2
-- pg 124: E-Let
    S.Let x t1 t2 -> do t1' <- eval_small t1; return $ S.Let x t1' t2
-- pg 34: E-IfTrue
    S.If (S.Const S.Tru) t2 _ -> return t2
-- pg 34: E-IfFalse
    S.If (S.Const S.Fls) _ t3 -> return t3
-- pg 34: E-If
    S.If t1 t2 t3 -> do t1' <- eval_small t1; return $ S.If t1' t2 t3
-- primops
    S.PrimApp op xs
        | all S.isValue xs -> return (S.primOpEval op xs)
        | otherwise          -> do xs' <- mapM eval_small xs; return $ S.PrimApp op xs'
-- pg 129: E-ProjRcd
    S.Project t1@(S.Record labelsAndTerms) l1
        | isValue t1 -> lookupOrElse l1 labelsAndTerms (l1 ++ " is not in " ++ show t1)
-- pg 129:E-Prog
    S.Project t1 l1 -> do t1' <- eval_small t1; return $ S.Project t1' l1
-- pg 129: E-Rcd
    S.Record labelsAndTerms -> do
        let vs = takeWhile (isValue . snd) labelsAndTerms
        let ((l1, t1):ts) = dropWhile (isValue . snd) labelsAndTerms
        t1' <- eval_small t1
        return $ Record (vs ++ [(l1, t1')] ++ ts)
-- pg 136: E-Case-Variant
    S.Case tag@(S.Tag l1 t1 _) lvt -> do
        let (labels, vars, terms) = unzip3 lvt
        x2 <- U.lookupOrElse l1 (zip labels vars) ("Invalid label in: " ++ show tag)
        t2 <- U.lookupOrElse l1 (zip labels terms) ("Invalid label in: " ++ show tag)
        Right (S.subst x2 t1 t2)
-- pg 136; E-Case
    S.Case t1 lvt -> do t1' <- eval_small t1; return $ S.Case t1' lvt
-- pg 136 E-Variant
    S.Tag l1 t1 tau1 -> do t1' <- eval_small t1; return $ S.Tag l1 t1' tau1
    S.Closure _ _ -> undefined
-- pg 276 E-Fld
    S.Fold tau1 t1 
        | S.isNotValue t1 -> do t1' <- eval_small t1; return $ S.Fold tau1 t1'
        | otherwise       -> return t
-- pg 276 E-UnfldFld
    S.Unfold tau1 (S.Fold tau2 t1)
        | S.isValue t1 -> return t1
        | otherwise    -> do t1' <- eval_small t1; return $ S.Unfold tau1 (S.Fold tau2 t1')
-- pg 276 E-Unfld
    S.Unfold tau1 t1
        | S.isNotValue t1 -> do t1' <- eval_small t1; return $ S.Unfold tau1 t1'
-- To catch things that are not pattern matched
    _ -> error (show t ++ " is not defined in eval_small")

--- Debug variant of small-step semantics
eval_small_trace :: S.Term -> Either String S.Term
eval_small_trace t -- return self
    | S.Const _  <- t =               do traceM ("Constant Value " ++ "\n" ++ (show t) ++ "\n\n\n")
                                         return t
    | S.Var _    <- t =               do traceM ("Variable Value" ++ "\n" ++ (show t) ++ "\n\n\n") 
                                         return t
    | S.Abs {}   <- t =               do traceM ("Abstraction Value " ++ "\n" ++ (show t) ++ "\n\n\n") 
                                         return t
eval_small_trace t = case t of
    S.ErrorTerm err ->                do traceM ("Error Term " ++ "\n" ++ (show t) ++ "\n\n\n") 
                                         (Left $ "something went wrong! term errored during small step evaluation: " ++ err)
    S.App t1@(S.Abs x _ t12) v2 
       | S.isValue v2 ->              do traceM ("Substituting Value Into App" ++ "\n" ++ (show t) ++ "\n\n\n") 
                                         return ((x |-> v2) t12)
    S.App v1 t2 
       | S.isValue v1 ->              do traceM ("Evaluating Second Argument of Application" ++ "\n" ++ (show t) ++ "\n\n\n")
                                         t2' <- eval_small_trace t2 
                                         return (S.App v1 t2')
    S.App t1 t2 ->                    do traceM ("Evaluating First Argument of Application" ++ "\n" ++ (show t) ++ "\n\n\n")
                                         t1' <-  eval_small_trace t1
                                         return (S.App t1' t2)
    S.Fix f@(S.Abs x _ t2) ->         do traceM ("Substituting a Single Iteration with Fix" ++ "\n" ++ (show t) ++ "\n\n\n")
                                         return ((x |-> S.Fix f) t2)
    S.Fix t1 ->                       do traceM ("Evaluating Term Within a Fix" ++ "\n" ++ (show t) ++ "\n\n\n")
                                         t1' <- eval_small_trace t1
                                         return (S.Fix t1')
    S.Let x v1 t2 
       | S.isValue v1 ->              do traceM ("Substituing Let Value into Term" ++ "\n" ++ (show t) ++ "\n\n\n")
                                         return ((x |-> v1) t2)
    S.Let x t1 t2 ->                  do traceM ("Evaluating First Argument of Let Term" ++ "\n" ++ (show t) ++ "\n\n\n")
                                         t1' <- eval_small_trace t1 
                                         return (S.Let x t1' t2)
    S.If (S.Const S.Tru) t2 _ ->      do traceM ("If Statement with True Condition" ++ "\n" ++ (show t) ++ "\n\n\n")
                                         return t2
    S.If (S.Const S.Fls) _ t3 ->      do traceM ("If Statement with False Condition" ++ "\n" ++ (show t) ++ "\n\n\n")
                                         return t3
    S.If t1 t2 t3 ->                  do traceM ("If Statement with Unevaluated Condition" ++ "\n" ++ (show t) ++ "\n\n\n")
                                         t1' <- eval_small_trace t1 
                                         return (S.If t1' t2 t3)
    S.PrimApp op xs
        | all S.isValue xs ->         do traceM ("PrimApp with All Values as Arguments" ++ "\n" ++ (show t) ++ "\n\n\n")
                                         return (S.primOpEval op xs)
        | otherwise          ->       do traceM ("PrimApp with Unevaluated Argument" ++ "\n" ++ (show t) ++ "\n\n\n")
                                         xs' <- mapM eval_small_trace xs 
                                         return (S.PrimApp op xs')
    S.Project t1@(S.Record labelsAndTerms) l1
        | isValue t1 ->               do traceM ("Projection with Value as Record" ++ "\n" ++ (show t) ++ "\n\n\n")
                                         lookupOrElse l1 labelsAndTerms (l1 ++ " is not in " ++ show t1)
    S.Project t1 l1 ->                do traceM ("Projection with Nonvalue as Record" ++ "\n" ++ (show t) ++ "\n\n\n")
                                         t1' <- eval_small_trace t1 
                                         return (S.Project t1' l1)
    S.Record labelsAndTerms ->        do traceM ("Evaluating Record" ++ "\n" ++ (show t) ++ "\n\n\n")
                                         let vs = takeWhile (isValue . snd) labelsAndTerms
                                         let ((l1, t1):ts) = dropWhile (isValue . snd) labelsAndTerms
                                         t1' <- eval_small_trace t1
                                         return (Record (vs ++ [(l1, t1')] ++ ts))
    S.Case tag@(S.Tag l1 t1 _) lvt -> do traceM ("Evaluating Case with Tag as First Argument" ++ "\n" ++ (show t) ++ "\n\n\n")
                                         let (labels, vars, terms) = unzip3 lvt
                                         x2 <- U.lookupOrElse l1 (zip labels vars) ("Invalid label in: " ++ show tag)
                                         t2 <- U.lookupOrElse l1 (zip labels terms) ("Invalid label in: " ++ show tag)
                                         return (S.subst x2 t1 t2)
    S.Case t1 lvt ->                  do traceM ("Evaluating Case with Non-tag First Argument" ++ "\n" ++ (show t) ++ "\n\n\n")
                                         t1' <- eval_small_trace t1 
                                         return (S.Case t1' lvt)
    S.Tag l1 t1 tau1 ->               do traceM ("Evaluating Tag" ++ "\n" ++ (show t) ++ "\n\n\n")
                                         t1' <- eval_small_trace t1 
                                         return (S.Tag l1 t1' tau1)
    S.Fold tau1 t1 
        | S.isNotValue t1 ->          do traceM ("Evaluating Fold when First Subterm is Nonvalue" ++ "\n" ++ (show t) ++ "\n\n\n")
                                         t1' <- eval_small_trace t1 
                                         return (S.Fold tau1 t1')
        | otherwise       ->          do traceM ("Evaluating Fold when First Subterm is Value" ++ "\n" ++ (show t) ++ "\n\n\n")
                                         return t
    S.Unfold tau1 t1@(S.Fold tau2 t2)
        | S.isValue t2 ->             do traceM ("Evaluating Unfold Fold with Inner Value" ++ "\n" ++ (show t) ++ "\n\n\n")
                                         return t2
        | otherwise    ->             do traceM ("Evaluating Unfold Fold with Inner Nonvalue" ++ "\n" ++ (show t) ++ "\n\n\n")
                                         t1' <- eval_small_trace t1 
                                         return (S.Unfold tau1 t1')
    S.Unfold tau1 t1
        | S.isNotValue t1 ->          do traceM ("Evaluating Inner Term of Unfold" ++ "\n" ++ (show t) ++ "\n\n\n")
                                         t1' <- eval_small_trace t1 
                                         return (S.Unfold tau1 t1')
    _ -> error (show t ++ " is not defined in eval_small")


eval :: S.Term -> S.Term
eval v | S.isValue v = v
eval t = case eval_small t {-`U.debug` (show t ++ "\n\n\n")-} of
        Right t' -> eval t'
        Left err -> S.ErrorTerm err

eval_trace :: S.Term -> S.Term
eval_trace t 
    | S.isValue t = t
    | otherwise = case eval_small_trace t of
                        Right t' -> eval_trace t'
                        Left err -> S.ErrorTerm err

eval_prime :: S.Term -> S.Term
eval_prime t = case eval_big t S.Empty of
    Right v  -> v
    Left err -> S.ErrorTerm err


