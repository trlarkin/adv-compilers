module MyErrorType where

import           Control.Monad

data Result a = ParseError String
              | TypeError String
              | FreeVarError String
              | EvaluationError String String
              | Valid a
              deriving (Eq, Show)

instance Functor Result where
    fmap = (<$>)

instance Applicative Result where
    pure = return
    (<*>) = ap

instance Monad Result where
    return = Valid
    Valid t >>= f                       = f t
    ParseError err >>= _                = ParseError err
    TypeError err >>= _                 = TypeError err
    FreeVarError err >>= _              = FreeVarError err
    EvaluationError evaluator err >>= _ = EvaluationError evaluator err

valid :: Result a -> Bool
valid (Valid _) = True
valid _         = False

sameValid :: Eq a => Result a -> Result a -> String
sameValid (Valid x) (Valid y)       = if x == y then "PASSING" else "FAILING"
sameValid (Valid _) _               = "UNKNOWN"
sameValid (ParseError err) _        = "PARSE FAIL"
sameValid (TypeError err) _         = "TYPE FAIL"
sameValid (FreeVarError err) _      = "FV FAIL"
sameValid (EvaluationError _ err) _ = "EVAL FAIL"
