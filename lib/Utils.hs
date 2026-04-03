module Utils where

import Debug.Trace

data BrokenList a b = BrokenList {
    pre :: [a],
    oddBall :: b,
    post :: [a]
}

headBL :: BrokenList a b -> Either a b
headBL (BrokenList [] b _) = Right b
headBL (BrokenList (a:_) _  _) = Left a


maybeToEither :: Maybe b -> a -> Either a b
maybeToEither (Just x) _ = Right x
maybeToEither Nothing y  = Left y

lookupOrElse :: Eq a => a -> [(a, b)] -> s -> Either s b
lookupOrElse x t s = case lookup x t of
  Just res -> Right res
  Nothing  -> Left s

debug :: c -> String -> c
debug = flip trace

-- equalOrElse :: Eq a => a -> a -> s -> Either s a
-- equalOrElse x y s
--   | x == y = Right True
