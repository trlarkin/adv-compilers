module NaturalSemanticsWithEnvironmentsClosuresAndDeBruijnIndices_CBV where

import           Data.Maybe
import qualified DeBruijnWithIntegerLabelsAndTags as S
import qualified IntegerArithmetic                as I

data Value = Clo S.Term Env
           | BoolVal Bool
           | IntVal I.IntegerType
           | CharVal Char
           | UnitVal
          --  | RecordVal [Value]
          --  | TagVal Int Value
          --  | FoldVal Value
           deriving Show

type Env = [Value]

evalInEnv :: Env -> S.Term -> Maybe Value
evalInEnv e t = case t of
  S.Var i         ->  Just (e!!i)
  S.Abs tau t1    ->  Just (Clo (S.Abs tau t1) e)
  S.App t1 t2     ->  do
                        Clo (S.Abs _ t') e' <- evalInEnv e t1
                        v' <- evalInEnv e t2
                        evalInEnv (v':e') t'
  S.PrimApp op ts -> do
                        vs' <- mapM (evalInEnv e) ts
                        let ts' = constUneval <$> vs'
                        let res = S.primOpEval op (S.Const <$> ts')
                        evalInEnv e res
  S.If t1 t2 t3   -> do
                        BoolVal b <- evalInEnv e t1
                        if b
                          then evalInEnv e t2
                          else evalInEnv e t3
  S.Let t1 t2   -> do
                        v' <- evalInEnv e t1
                        evalInEnv (v':e) t2
  S.Fix t1        -> do  -- fix (\x.t) -> [x |-> fix (\x.t)] t
                        Clo (S.Abs _ tBody) e' <- evalInEnv e t1
                        let eRec = (Clo tBody [eRec])
                        evalInEnv (eRec:e') tBody
  S.Const c -> return $ constEval c
  _               -> error ("not valid for nat semantics DeBruijn: " ++ show t)


constEval :: S.Const -> Value
constEval c = case c of
  S.Tru           ->  BoolVal True
  S.Fls           ->  BoolVal False
  S.IntConst i    ->  IntVal i
  S.CharConst cst ->  CharVal cst
  S.Unit          ->  UnitVal

constUneval :: Value -> S.Const
constUneval c = case c of
  BoolVal True  ->  S.Tru
  BoolVal False ->  S.Fls
  IntVal i      ->  S.IntConst i
  CharVal c     ->  S.CharConst c
  UnitVal       ->  S.Unit
  _             -> S.CharConst 'X'

primOpEval :: S.PrimOp -> [Value] -> Value
primOpEval p vs = let S.Const c = S.primOpEval p (map (S.Const . constUneval) vs)
                  in constEval c

eval :: S.Term -> Value
eval t = fromJust (evalInEnv [] t)

evalToTerm :: S.Term -> S.Term
evalToTerm = S.Const . constUneval . eval
