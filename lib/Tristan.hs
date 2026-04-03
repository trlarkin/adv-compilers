
-- data PrimConst = True | False | IntPC Int

-- newtype Var = Var String
-- newtype Const = Const PrimConst
-- data Abs t1 t2 = Abs Var t1 t2

-- class Value v where
--     val :: v -> Int

-- instance Value Var where
--     val v = 0

-- instance Value Const where
--     val v = 1

-- instance Value v1 => Value (Abs v1 t2) where
--     val v = 2

data Term = V Value | NV NonValue

data Value = Const Int
           | Abs String Term

data NonValue = Add Term Term
              | App Term Term

isValue :: Term -> Bool
isValue (V _)  = True
isValue (NV _) = False
