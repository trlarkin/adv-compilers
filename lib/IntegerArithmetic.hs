module IntegerArithmetic where

import Data.Int
import Data.Bits
import Data.Char

type IntegerType = Int64

intAdd :: IntegerType -> IntegerType -> IntegerType
intAdd m n = m + n

intSub :: IntegerType -> IntegerType -> IntegerType
intSub m n = m - n

intMul :: IntegerType -> IntegerType -> IntegerType
intMul m n = m * n

intDiv :: IntegerType -> IntegerType -> IntegerType
intDiv m n  =  if n == 0 then error "integer division by zero" else m `div` n

intNand :: IntegerType -> IntegerType -> IntegerType
intNand m n = complement (m .&. n)

intEq :: IntegerType -> IntegerType -> Bool
intEq m n  =  m == n

intLt :: IntegerType -> IntegerType -> Bool
intLt m n  =  m < n

intOrd :: Char -> IntegerType
intOrd c = fromIntegral (ord c)

intChr :: IntegerType -> Char
intChr i = if 0 <= i && i <= 255 then chr (fromIntegral i) else error "integer out of range for character"

